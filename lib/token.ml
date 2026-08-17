(* Token definitions for the Kite bootstrap subset.
   Surface syntax is Kotlin-flavored: expression-oriented, `fun`/`val`/`var`,
   null-safety operators (`?`, `?.`, `?:`, `!!`), `when`, data structs,
   string interpolation (`"$x ${e}"`), and Go-style newline terminators. *)

type token =
  (* literals *)
  | INT of int
  | FLOAT of float
  | STRING of string
  | CHAR of int            (* char literal, stored as a code point (ASCII in bootstrap) *)
  | INTERP of ipart list   (* interpolated string: ordered literal/expr parts *)
  | IDENT of string
  (* keywords *)
  | FUN
  | VAL
  | VAR
  | IF
  | ELSE
  | WHILE
  | FOR
  | RETURN
  | WHEN
  | IS
  | IN
  | AS
  | STRUCT
  | CLASS
  | ENUM
  | DEINIT
  | PUB
  | IMPORT
  | TRUE
  | FALSE
  | NULL
  | THIS
  | SELF
  | MUT
  | CONSUMING
  | INOUT
  | TRAIT
  | IMPL
  | WHERE
  | BREAK
  | CONTINUE
  (* grouping / punctuation *)
  | LPAREN
  | RPAREN
  | LBRACE
  | RBRACE
  | LBRACKET
  | RBRACKET
  | COMMA
  | DOT
  | DOTDOT (* .. range *)
  | COLON
  | COLONCOLON (* :: *)
  | SEMI
  | ARROW (* -> *)
  | FATARROW (* => *)
  (* operators *)
  | ASSIGN (* = *)
  | EQ (* == *)
  | NEQ (* != *)
  | LT
  | GT
  | LE
  | GE
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | PERCENT
  | NOT (* ! *)
  | ANDAND (* && *)
  | OROR (* || *)
  | PIPE (* | — or-pattern separator / bitwise or *)
  | AMP (* & — bitwise and *)
  | CARET (* ^ — bitwise xor *)
  | SHL (* << *)
  | SHR (* >> *)
  | QUESTION (* ?  nullable type marker *)
  | QDOT (* ?. safe call *)
  | ELVIS (* ?: *)
  | BANGBANG (* !! non-null assertion *)
  | AT (* @ annotation marker *)
  | NEWLINE (* soft statement terminator, inserted by ATI *)
  | EOF

and ipart =
  | IStr of string          (* a literal chunk of the string *)
  | ICode of located list   (* an embedded expression, already lexed (ends with EOF) *)

(* A token annotated with its source position (1-based line, 1-based column). *)
and located = {
  tok : token;
  line : int;
  col : int;
}

let keyword_of_string = function
  | "fun" -> Some FUN
  | "val" -> Some VAL
  | "var" -> Some VAR
  | "if" -> Some IF
  | "else" -> Some ELSE
  | "while" -> Some WHILE
  | "for" -> Some FOR
  | "return" -> Some RETURN
  | "when" -> Some WHEN
  | "is" -> Some IS
  | "in" -> Some IN
  | "as" -> Some AS
  | "struct" -> Some STRUCT
  | "class" -> Some CLASS
  | "enum" -> Some ENUM
  | "deinit" -> Some DEINIT
  | "pub" -> Some PUB
  | "import" -> Some IMPORT
  | "true" -> Some TRUE
  | "false" -> Some FALSE
  | "null" -> Some NULL
  | "this" -> Some THIS
  | "self" -> Some SELF
  | "mut" -> Some MUT
  | "consuming" -> Some CONSUMING
  | "inout" -> Some INOUT
  | "trait" -> Some TRAIT
  | "impl" -> Some IMPL
  | "where" -> Some WHERE
  | "break" -> Some BREAK
  | "continue" -> Some CONTINUE
  | _ -> None

let rec to_string = function
  | INT n -> Printf.sprintf "INT(%d)" n
  | FLOAT f -> Printf.sprintf "FLOAT(%g)" f
  | STRING s -> Printf.sprintf "STRING(%S)" s
  | CHAR c -> Printf.sprintf "CHAR(%d)" c
  | INTERP parts -> "INTERP[" ^ String.concat "; " (List.map ipart_to_string parts) ^ "]"
  | IDENT s -> Printf.sprintf "IDENT(%s)" s
  | FUN -> "FUN"
  | VAL -> "VAL"
  | VAR -> "VAR"
  | IF -> "IF"
  | ELSE -> "ELSE"
  | WHILE -> "WHILE"
  | FOR -> "FOR"
  | RETURN -> "RETURN"
  | WHEN -> "WHEN"
  | IS -> "IS"
  | IN -> "IN"
  | AS -> "AS"
  | STRUCT -> "STRUCT"
  | CLASS -> "CLASS"
  | ENUM -> "ENUM"
  | DEINIT -> "DEINIT"
  | PUB -> "PUB"
  | IMPORT -> "IMPORT"
  | TRUE -> "TRUE"
  | FALSE -> "FALSE"
  | NULL -> "NULL"
  | THIS -> "THIS"
  | SELF -> "SELF"
  | MUT -> "MUT"
  | CONSUMING -> "CONSUMING"
  | INOUT -> "INOUT"
  | TRAIT -> "TRAIT"
  | IMPL -> "IMPL"
  | WHERE -> "WHERE"
  | BREAK -> "BREAK"
  | CONTINUE -> "CONTINUE"
  | LPAREN -> "LPAREN"
  | RPAREN -> "RPAREN"
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | LBRACKET -> "LBRACKET"
  | RBRACKET -> "RBRACKET"
  | COMMA -> "COMMA"
  | DOT -> "DOT"
  | DOTDOT -> "DOTDOT"
  | COLON -> "COLON"
  | COLONCOLON -> "COLONCOLON"
  | SEMI -> "SEMI"
  | ARROW -> "ARROW"
  | FATARROW -> "FATARROW"
  | ASSIGN -> "ASSIGN"
  | EQ -> "EQ"
  | NEQ -> "NEQ"
  | LT -> "LT"
  | GT -> "GT"
  | LE -> "LE"
  | GE -> "GE"
  | PLUS -> "PLUS"
  | MINUS -> "MINUS"
  | STAR -> "STAR"
  | SLASH -> "SLASH"
  | PERCENT -> "PERCENT"
  | NOT -> "NOT"
  | ANDAND -> "ANDAND"
  | OROR -> "OROR"
  | PIPE -> "PIPE"
  | AMP -> "AMP"
  | CARET -> "CARET"
  | SHL -> "SHL"
  | SHR -> "SHR"
  | QUESTION -> "QUESTION"
  | QDOT -> "QDOT"
  | ELVIS -> "ELVIS"
  | BANGBANG -> "BANGBANG"
  | AT -> "AT"
  | NEWLINE -> "NEWLINE"
  | EOF -> "EOF"

and ipart_to_string = function
  | IStr s -> Printf.sprintf "str %S" s
  | ICode toks ->
    let inner =
      toks
      |> List.filter (fun l -> l.tok <> EOF)
      |> List.map (fun l -> to_string l.tok)
      |> String.concat " "
    in
    "expr(" ^ inner ^ ")"
