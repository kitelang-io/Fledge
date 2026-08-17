(* Hand-written lexer for the Kite bootstrap subset.

   Two notable behaviours beyond a plain tokenizer:

   - Go-style automatic terminator insertion (ATI): a NEWLINE token is emitted
     at a line break only when the previous token can end a statement AND the
     next token does not obviously continue it (a leading `.`/`?.` keeps a method
     chain going). This lets statements be newline-terminated without semicolons.
     A continuation line must still not *begin* with a binary operator; wrap long
     expressions in parens.

   - String interpolation: `"$name"` and `"${ expr }"`. `$name` captures a single
     identifier; `${ ... }` captures a full expression (lexed recursively). A
     string with no interpolation lexes to a plain STRING, as before. *)

open Token

exception Lex_error of string * int * int (* message, line, col *)

type state = {
  src : string;
  len : int;
  mutable pos : int;
  mutable line : int;
  mutable col : int;
}

let make src = { src; len = String.length src; pos = 0; line = 1; col = 1 }

let peek st = if st.pos < st.len then Some st.src.[st.pos] else None
let peek2 st = if st.pos + 1 < st.len then Some st.src.[st.pos + 1] else None

let advance st =
  let c = st.src.[st.pos] in
  st.pos <- st.pos + 1;
  if c = '\n' then begin
    st.line <- st.line + 1;
    st.col <- 1
  end
  else st.col <- st.col + 1;
  c

let is_digit c = c >= '0' && c <= '9'
let is_alpha c = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c = '_'
let is_alnum c = is_alpha c || is_digit c

(* consume a `//` line comment or `/* */` (nesting) block comment; returns true
   if it consumed one, false if the `/` starts an operator instead. *)
let skip_comment st =
  match peek st, peek2 st with
  | Some '/', Some '/' ->
    ignore (advance st);
    ignore (advance st);
    let rec loop () =
      match peek st with
      | Some '\n' | None -> ()
      | Some _ -> ignore (advance st); loop ()
    in
    loop ();
    true
  | Some '/', Some '*' ->
    ignore (advance st);
    ignore (advance st);
    let rec loop depth =
      if depth = 0 then ()
      else
        match peek st, peek2 st with
        | Some '/', Some '*' -> ignore (advance st); ignore (advance st); loop (depth + 1)
        | Some '*', Some '/' -> ignore (advance st); ignore (advance st); loop (depth - 1)
        | Some _, _ -> ignore (advance st); loop depth
        | None, _ -> raise (Lex_error ("unterminated block comment", st.line, st.col))
    in
    loop 1;
    true
  | _ -> false

(* skip whitespace and comments; return whether a line break was crossed
   (detected via the line counter, so newlines inside comments count too). *)
let skip_trivia st =
  let l0 = st.line in
  let rec go () =
    match peek st with
    | Some (' ' | '\t' | '\r' | '\n') -> ignore (advance st); go ()
    | Some '/' -> if skip_comment st then go () else ()
    | _ -> ()
  in
  go ();
  st.line <> l0

let is_hex_digit c =
  (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

let read_number st =
  let start = st.pos and l0 = st.line and c0 = st.col in
  (* hex literal `0x...` — int_of_string parses the "0x" form directly *)
  if peek st = Some '0' && (peek2 st = Some 'x' || peek2 st = Some 'X') then begin
    ignore (advance st); ignore (advance st);
    while (match peek st with Some c -> is_hex_digit c | None -> false) do ignore (advance st) done;
    let text = String.sub st.src start (st.pos - start) in
    (try INT (int_of_string text)
     with Failure _ -> raise (Lex_error ("malformed hex literal `" ^ text ^ "`", l0, c0)))
  end else begin
  while (match peek st with Some c -> is_digit c | None -> false) do
    ignore (advance st)
  done;
  (* fractional part: a '.' followed by a digit (so `1..5` stays a range) *)
  let is_float =
    match peek st, peek2 st with
    | Some '.', Some d when is_digit d ->
      ignore (advance st);
      while (match peek st with Some c -> is_digit c | None -> false) do
        ignore (advance st)
      done;
      true
    | _ -> false
  in
  let text = String.sub st.src start (st.pos - start) in
  (* int_of_string / float_of_string raise Failure on an out-of-range literal;
     turn that into a positioned Lex_error instead of crashing the whole tool. *)
  if is_float then
    (try FLOAT (float_of_string text)
     with Failure _ -> raise (Lex_error ("malformed float literal `" ^ text ^ "`", l0, c0)))
  else
    (try INT (int_of_string text)
     with Failure _ -> raise (Lex_error ("integer literal out of range `" ^ text ^ "`", l0, c0)))
  end

let read_ident st =
  let start = st.pos in
  while (match peek st with Some c -> is_alnum c | None -> false) do
    ignore (advance st)
  done;
  let text = String.sub st.src start (st.pos - start) in
  match keyword_of_string text with Some kw -> kw | None -> IDENT text

(* read a `'c'` char literal (ASCII + simple escapes in bootstrap) *)
let read_char st =
  ignore (advance st); (* opening ' *)
  let code =
    match peek st with
    | None -> raise (Lex_error ("unterminated char literal", st.line, st.col))
    | Some '\\' ->
      ignore (advance st);
      (match peek st with
       | Some 'n' -> ignore (advance st); Char.code '\n'
       | Some 't' -> ignore (advance st); Char.code '\t'
       | Some 'r' -> ignore (advance st); Char.code '\r'
       | Some '\\' -> ignore (advance st); Char.code '\\'
       | Some '\'' -> ignore (advance st); Char.code '\''
       | Some '0' -> ignore (advance st); 0
       | Some c -> raise (Lex_error (Printf.sprintf "invalid escape \\%c in char literal" c, st.line, st.col))
       | None -> raise (Lex_error ("unterminated char escape", st.line, st.col)))
    | Some c -> ignore (advance st); Char.code c
  in
  (match peek st with
   | Some '\'' -> ignore (advance st)
   | _ -> raise (Lex_error ("expected closing ' in char literal", st.line, st.col)));
  CHAR code

(* a token that, as the last on a line, can terminate a statement (ATI) *)
let can_end = function
  | INT _ | FLOAT _ | STRING _ | CHAR _ | INTERP _ | IDENT _
  | TRUE | FALSE | NULL | THIS
  | RETURN | BREAK | CONTINUE
  | RPAREN | RBRACKET | RBRACE | BANGBANG | QUESTION -> true
  | _ -> false

let read_escape st buf =
  ignore (advance st); (* the backslash *)
  match peek st with
  | Some 'n' -> Buffer.add_char buf '\n'; ignore (advance st)
  | Some 't' -> Buffer.add_char buf '\t'; ignore (advance st)
  | Some 'r' -> Buffer.add_char buf '\r'; ignore (advance st)
  | Some '\\' -> Buffer.add_char buf '\\'; ignore (advance st)
  | Some '"' -> Buffer.add_char buf '"'; ignore (advance st)
  | Some '$' -> Buffer.add_char buf '$'; ignore (advance st)
  | Some '0' -> Buffer.add_char buf '\000'; ignore (advance st)
  | Some c -> raise (Lex_error (Printf.sprintf "invalid escape \\%c" c, st.line, st.col))
  | None -> raise (Lex_error ("unterminated escape", st.line, st.col))

let rec tokenize (src : string) : located list =
  let st = make src in
  (* start as if just after a NEWLINE so no spurious leading terminator *)
  let rec loop acc last =
    let saw_nl = skip_trivia st in
    let line = st.line and col = st.col in
    match peek st with
    | None -> List.rev ({ tok = EOF; line; col } :: acc)
    | Some _ ->
      (* a leading `.` or `?.` continues the previous line (method chains) *)
      let next_continues =
        match peek st with
        | Some '.' -> true
        | Some '?' -> peek2 st = Some '.'
        | _ -> false
      in
      if saw_nl && can_end last && not next_continues then
        loop ({ tok = NEWLINE; line; col } :: acc) NEWLINE
      else
        let tok = read_token st in
        loop ({ tok; line; col } :: acc) tok
  in
  loop [] NEWLINE

and read_token st =
  let c = st.src.[st.pos] in
  if is_digit c then read_number st
  else if is_alpha c then read_ident st
  else if c = '"' then read_interp st ~line:st.line ~col:st.col
  else if c = '\'' then read_char st
  else begin
    ignore (advance st);
    let two want tok fallback =
      match peek st with
      | Some c2 when c2 = want -> ignore (advance st); tok
      | _ -> fallback
    in
    match c with
    | '(' -> LPAREN
    | ')' -> RPAREN
    | '{' -> LBRACE
    | '}' -> RBRACE
    | '[' -> LBRACKET
    | ']' -> RBRACKET
    | ',' -> COMMA
    | ';' -> SEMI
    | '@' -> AT
    | '.' -> two '.' DOTDOT DOT
    | ':' -> two ':' COLONCOLON COLON
    | '+' -> PLUS
    | '*' -> STAR
    | '/' -> SLASH
    | '%' -> PERCENT
    | '^' -> CARET
    | '-' -> two '>' ARROW MINUS
    | '=' -> (match peek st with
        | Some '=' -> ignore (advance st); EQ
        | Some '>' -> ignore (advance st); FATARROW
        | _ -> ASSIGN)
    | '!' -> (match peek st with
        | Some '=' -> ignore (advance st); NEQ
        | Some '!' -> ignore (advance st); BANGBANG
        | _ -> NOT)
    | '<' -> (match peek st with
        | Some '=' -> ignore (advance st); LE
        | Some '<' -> ignore (advance st); SHL
        | _ -> LT)
    | '>' -> (match peek st with
        | Some '=' -> ignore (advance st); GE
        | Some '>' -> ignore (advance st); SHR
        | _ -> GT)
    | '&' -> (match peek st with
        | Some '&' -> ignore (advance st); ANDAND
        | _ -> AMP)
    | '|' -> (match peek st with
        | Some '|' -> ignore (advance st); OROR
        | _ -> PIPE)
    | '?' -> (match peek st with
        | Some '.' -> ignore (advance st); QDOT
        | Some ':' -> ignore (advance st); ELVIS
        | _ -> QUESTION)
    | _ -> raise (Lex_error (Printf.sprintf "unexpected character %C" c, st.line, st.col))
  end

(* read a `"..."` or `"""..."""` string. A triple-quoted string spans lines and
   applies no backslash escapes (raw), but still interpolates `$x`/`${e}`
   (Kotlin-style). Produces STRING when there is no interpolation, INTERP (a list
   of literal/expression parts) when there is. *)
and read_interp st ~line ~col =
  let triple =
    st.pos + 2 < st.len && st.src.[st.pos + 1] = '"' && st.src.[st.pos + 2] = '"'
  in
  ignore (advance st); (* opening quote *)
  if triple then (ignore (advance st); ignore (advance st));
  let parts = ref [] in
  let buf = Buffer.create 16 in
  let flush () =
    if Buffer.length buf > 0 then begin
      parts := IStr (Buffer.contents buf) :: !parts;
      Buffer.clear buf
    end
  in
  let at_close () =
    if triple then
      peek st = Some '"' && peek2 st = Some '"'
      && st.pos + 2 < st.len && st.src.[st.pos + 2] = '"'
    else peek st = Some '"'
  in
  let rec loop () =
    if at_close () then begin
      ignore (advance st);
      if triple then (ignore (advance st); ignore (advance st));
      flush ()
    end
    else
    match peek st with
    | None -> raise (Lex_error ("unterminated string literal", line, col))
    | Some '\\' when not triple -> read_escape st buf; loop ()
    | Some '$' when (match peek2 st with Some '{' -> true | _ -> false) ->
      flush ();
      ignore (advance st); (* $ *)
      ignore (advance st); (* { *)
      let start = st.pos in
      let depth = ref 1 in
      let scanning = ref true in
      while !scanning do
        match peek st with
        | None -> raise (Lex_error ("unterminated ${...} interpolation", line, col))
        | Some '{' -> depth := !depth + 1; ignore (advance st)
        | Some '}' ->
          decr depth;
          if !depth = 0 then scanning := false else ignore (advance st)
        | Some _ -> ignore (advance st)
      done;
      let sub = String.sub st.src start (st.pos - start) in
      ignore (advance st); (* closing } *)
      parts := ICode (tokenize sub) :: !parts;
      loop ()
    | Some '$' when (match peek2 st with Some c -> is_alpha c | None -> false) ->
      flush ();
      let dline = st.line and dcol = st.col in
      ignore (advance st); (* $ *)
      let s0 = st.pos in
      while (match peek st with Some c -> is_alnum c | None -> false) do
        ignore (advance st)
      done;
      let name = String.sub st.src s0 (st.pos - s0) in
      parts :=
        ICode [ { tok = IDENT name; line = dline; col = dcol }; { tok = EOF; line = dline; col = dcol } ]
        :: !parts;
      loop ()
    | Some _ -> Buffer.add_char buf (advance st); loop ()
  in
  loop ();
  let parts = List.rev !parts in
  (* no embedded expression => a plain string literal *)
  if List.for_all (function IStr _ -> true | ICode _ -> false) parts then
    STRING (String.concat "" (List.map (function IStr s -> s | ICode _ -> "") parts))
  else INTERP parts
