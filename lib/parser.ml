(* Recursive-descent parser for declarations/statements, with a Pratt
   (precedence-climbing) core for expressions.

   Separators: the lexer performs Go-style automatic token insertion, emitting a
   NEWLINE after any line-final token that can end a statement; `skip_nl` consumes
   those (and explicit `;`) between statements and `when` arms. A continuation
   line must therefore not *begin* with a binary operator — wrap long expressions
   in parentheses so the line stays open. *)

open Token
open Ast

exception Parse_error of string * int * int (* message, line, col *)

type t = {
  toks : Token.located array;
  mutable idx : int;
}

let make toks = { toks = Array.of_list toks; idx = 0 }
let cur p = p.toks.(p.idx)
let peek p = (cur p).tok
let peek_at p n =
  let i = p.idx + n in
  if i < Array.length p.toks then p.toks.(i).tok else EOF

let err p msg =
  let l = cur p in
  raise (Parse_error (msg, l.line, l.col))

let advance p =
  let t = cur p in
  if p.idx < Array.length p.toks - 1 then p.idx <- p.idx + 1;
  t.tok

let eat p tok =
  if peek p = tok then ignore (advance p)
  else err p (Printf.sprintf "expected %s but found %s" (Token.to_string tok) (Token.to_string (peek p)))

let accept p tok = if peek p = tok then (ignore (advance p); true) else false

(* skip soft statement separators (NEWLINE from ATI, and explicit `;`) *)
let rec skip_nl p =
  match peek p with
  | NEWLINE | SEMI -> ignore (advance p); skip_nl p
  | _ -> ()

let ident p =
  match peek p with
  | IDENT s -> ignore (advance p); s
  | _ -> err p "expected an identifier"

(* ---- types ---- *)

let rec parse_type p =
  let base =
    match peek p with
    | LPAREN ->
      (* function type: (A, B) -> R *)
      ignore (advance p);
      let args = ref [] in
      if peek p <> RPAREN then begin
        args := [ parse_type p ];
        while accept p COMMA do args := parse_type p :: !args done
      end;
      eat p RPAREN;
      eat p ARROW;
      TyFun (List.rev !args, parse_type p)
    | IDENT _ ->
      let path = ref [ ident p ] in
      while accept p COLONCOLON do path := ident p :: !path done;
      let targs = if peek p = LT then parse_type_args p else [] in
      TyPath (List.rev !path, targs)
    | _ -> err p "expected a type"
  in
  let rec nullable t = if accept p QUESTION then nullable (TyNullable t) else t in
  nullable base

and parse_type_args p =
  eat p LT;
  let args = ref [ parse_type p ] in
  while accept p COMMA do args := parse_type p :: !args done;
  eat p GT;
  List.rev !args

(* ---- expressions (Pratt) ---- *)

(* left/right binding powers; left-associative => rbp = lbp + 1 *)
and infix_bp = function
  | OROR -> Some (1, 2)
  | ANDAND -> Some (3, 4)
  | PIPE -> Some (5, 6)
  | CARET -> Some (7, 8)
  | AMP -> Some (9, 10)
  | EQ | NEQ -> Some (11, 12)
  | LT | GT | LE | GE -> Some (13, 14)
  | SHL | SHR -> Some (15, 16)
  | DOTDOT -> Some (17, 18)
  | PLUS | MINUS -> Some (19, 20)
  | STAR | SLASH | PERCENT -> Some (21, 22)
  | _ -> None

and binop_of_tok = function
  | PLUS -> Add | MINUS -> Sub | STAR -> Mul | SLASH -> Div | PERCENT -> Mod
  | EQ -> Eq | NEQ -> Neq | LT -> Lt | GT -> Gt | LE -> Le | GE -> Ge
  | ANDAND -> And | OROR -> Or | DOTDOT -> Range
  | AMP -> BAnd | PIPE -> BOr | CARET -> BXor | SHL -> Shl | SHR -> Shr
  | _ -> assert false

and parse_expr p min_bp =
  let left = ref (parse_prefix p) in
  let continue = ref true in
  while !continue do
    (* elvis is handled as its own node, lower than the arithmetic table *)
    match peek p with
    | ELVIS when min_bp <= 0 ->
      ignore (advance p);
      let rhs = parse_expr p 1 in
      left := Elvis (!left, rhs)
    | tok ->
      (match infix_bp tok with
       | Some (lbp, rbp) when lbp >= min_bp ->
         ignore (advance p);
         let rhs = parse_expr p rbp in
         left := Binary (binop_of_tok tok, !left, rhs)
       | _ -> continue := false)
  done;
  !left

and parse_prefix p =
  match peek p with
  | MINUS -> ignore (advance p); Unary (Neg, parse_prefix p)
  | NOT -> ignore (advance p); Unary (Not, parse_prefix p)
  | _ -> parse_postfix p

and parse_postfix p =
  let e = ref (parse_primary p) in
  let continue = ref true in
  while !continue do
    match peek p with
    | DOT -> ignore (advance p); e := Field (!e, ident p)
    | QDOT -> ignore (advance p); e := SafeField (!e, ident p)
    | COLONCOLON ->
      ignore (advance p);
      if peek p = LT then e := TypeApp (!e, parse_type_args p)
      else e := Static (!e, ident p)
    | BANGBANG -> ignore (advance p); e := NotNull !e
    | LPAREN -> ignore (advance p); e := Call (!e, parse_args p)
    | LBRACKET ->
      ignore (advance p);
      skip_nl p;
      let idx = parse_expr p 0 in
      skip_nl p;
      eat p RBRACKET;
      e := Index (!e, idx)
    | LBRACE ->
      (* trailing lambda: `f { ... }` / `xs.map { it * 2 }` *)
      let larg = { arg_name = None; arg_val = parse_trailing_lambda p } in
      (match !e with
       | Call (f, args) -> e := Call (f, args @ [ larg ])
       | _ -> e := Call (!e, [ larg ]))
    | _ -> continue := false
  done;
  !e

and parse_arg p =
  match peek p with
  | IDENT s when peek_at p 1 = ASSIGN ->
    ignore (advance p); ignore (advance p);
    { arg_name = Some s; arg_val = parse_expr p 0 }
  | _ -> { arg_name = None; arg_val = parse_expr p 0 }

and parse_args p =
  skip_nl p;
  if peek p = RPAREN then (ignore (advance p); [])
  else begin
    let args = ref [ parse_arg p ] in
    skip_nl p;
    while accept p COMMA do
      skip_nl p;
      if peek p <> RPAREN then (args := parse_arg p :: !args; skip_nl p)
    done;
    eat p RPAREN;
    List.rev !args
  end

and parse_primary p =
  match peek p with
  | INT n -> ignore (advance p); IntLit n
  | FLOAT f -> ignore (advance p); FloatLit f
  | STRING s -> ignore (advance p); StringLit s
  | CHAR c -> ignore (advance p); CharLit c
  | TRUE -> ignore (advance p); BoolLit true
  | FALSE -> ignore (advance p); BoolLit false
  | NULL -> ignore (advance p); NullLit
  | THIS -> ignore (advance p); This
  | SELF -> ignore (advance p); This
  | IDENT s -> ignore (advance p); Ident s
  | LPAREN ->
    ignore (advance p);
    let e = parse_expr p 0 in
    eat p RPAREN;
    e
  | LBRACE ->
    ignore (advance p);
    skip_nl p;
    (match try_lambda_params p with
     | Some params -> Lambda (params, parse_block_body p)
     | None -> parse_block_body p)
  | IF -> parse_if p
  | WHEN -> parse_when p
  | RETURN ->
    ignore (advance p);
    let stop =
      match peek p with
      | NEWLINE | SEMI | RBRACE | RPAREN | RBRACKET | COMMA | EOF | ELSE | ARROW | PIPE -> true
      | _ -> false
    in
    EReturn (if stop then None else Some (parse_expr p 0))
  | BREAK -> ignore (advance p); EBreak
  | CONTINUE -> ignore (advance p); EContinue
  | LBRACKET ->
    ignore (advance p);
    skip_nl p;
    if peek p = RBRACKET then (ignore (advance p); ListLit [])
    else begin
      let first = parse_expr p 0 in
      if accept p COLON then begin
        (* map literal ["k": v, ...] *)
        let v1 = parse_expr p 0 in
        let entries = ref [ (first, v1) ] in
        skip_nl p;
        while accept p COMMA do
          skip_nl p;
          if peek p <> RBRACKET then begin
            let k = parse_expr p 0 in
            eat p COLON;
            let v = parse_expr p 0 in
            entries := (k, v) :: !entries;
            skip_nl p
          end
        done;
        eat p RBRACKET;
        MapLit (List.rev !entries)
      end
      else begin
        (* list literal [a, b, ...] *)
        let elems = ref [ first ] in
        skip_nl p;
        while accept p COMMA do
          skip_nl p;
          if peek p <> RBRACKET then (elems := parse_expr p 0 :: !elems; skip_nl p)
        done;
        eat p RBRACKET;
        ListLit (List.rev !elems)
      end
    end
  | INTERP parts ->
    ignore (advance p);
    Interp
      (List.map
         (fun part ->
           match part with
           | Token.IStr s -> ILit s
           | Token.ICode toks -> IExpr (parse_interp_sub toks))
         parts)
  | _ -> err p "expected an expression"

and parse_interp_sub toks =
  let sub = make toks in
  parse_expr sub 0

and parse_if p =
  eat p IF;
  eat p LPAREN;
  let cond = parse_expr p 0 in
  eat p RPAREN;
  skip_nl p; (* the then-branch may sit on the next line *)
  let then_ = parse_expr p 0 in
  (* allow `} else` across a line break, but keep the NEWLINE as a separator
     when there is no else *)
  let saved = p.idx in
  skip_nl p;
  let else_ =
    if peek p = ELSE then (ignore (advance p); skip_nl p; Some (parse_expr p 0))
    else (p.idx <- saved; None)
  in
  If (cond, then_, else_)

and parse_when p =
  eat p WHEN;
  let subject =
    if peek p = LPAREN then begin
      ignore (advance p);
      skip_nl p;
      let ws_bind =
        if peek p = VAL
           && (match peek_at p 1 with IDENT _ -> true | _ -> false)
           && peek_at p 2 = ASSIGN
        then begin
          ignore (advance p); (* val *)
          let name = ident p in
          eat p ASSIGN;
          Some name
        end
        else None
      in
      let ws_expr = parse_expr p 0 in
      skip_nl p;
      eat p RPAREN;
      Some { ws_bind; ws_consuming = false; ws_expr }
    end
    else None
  in
  eat p LBRACE;
  skip_nl p;
  let arms = ref [] in
  while peek p <> RBRACE do
    let wa_lhs =
      if accept p ELSE then LhsElse
      else if subject = None then LhsCond (parse_expr p 0)
      else begin
        let pats = ref [ parse_pattern p ] in
        while accept p PIPE do pats := parse_pattern p :: !pats done;
        LhsPatterns (List.rev !pats)
      end
    in
    let wa_guard =
      if subject <> None && accept p IF then Some (parse_expr p 0) else None
    in
    eat p ARROW;
    let wa_body = parse_expr p 0 in
    arms := { wa_lhs; wa_guard; wa_body } :: !arms;
    skip_nl p
  done;
  eat p RBRACE;
  When (subject, List.rev !arms)

and parse_pattern p =
  match peek p with
  | INT n -> ignore (advance p); PLitInt n
  | FLOAT f -> ignore (advance p); PLitFloat f
  | STRING s -> ignore (advance p); PLitString s
  | CHAR c -> ignore (advance p); PLitChar c
  | TRUE -> ignore (advance p); PLitBool true
  | FALSE -> ignore (advance p); PLitBool false
  | NULL -> ignore (advance p); PLitNull
  | MINUS ->
    ignore (advance p);
    (match peek p with
     | INT n -> ignore (advance p); PLitInt (-n)
     | FLOAT f -> ignore (advance p); PLitFloat (-.f)
     | _ -> err p "expected a number after '-' in a pattern")
  | IS -> ignore (advance p); PIs (parse_type p, false)
  | IN -> ignore (advance p); PIn (parse_expr p 0, false)
  | NOT when peek_at p 1 = IS -> ignore (advance p); ignore (advance p); PIs (parse_type p, true)
  | NOT when peek_at p 1 = IN -> ignore (advance p); ignore (advance p); PIn (parse_expr p 0, true)
  | IDENT "_" -> ignore (advance p); PWild
  | IDENT s ->
    ignore (advance p);
    if s.[0] >= 'A' && s.[0] <= 'Z' then begin
      let path = ref [ s ] in
      while accept p COLONCOLON do path := ident p :: !path done;
      let path = List.rev !path in
      if peek p = LPAREN then PCtor (path, parse_ctor_pat_args p) else PPath path
    end
    else PBind s
  | _ -> err p "expected a pattern"

and parse_ctor_pat_args p =
  eat p LPAREN;
  skip_nl p;
  let parse_one () =
    match peek p with
    | DOTDOT -> ignore (advance p); `Rest
    | IDENT s when s.[0] >= 'a' && s.[0] <= 'z' && peek_at p 1 = ASSIGN ->
      ignore (advance p); ignore (advance p);
      `Named (s, parse_pattern p)
    | _ -> `Pat (parse_pattern p)
  in
  let args = ref [] in
  if peek p <> RPAREN then begin
    args := [ parse_one () ];
    skip_nl p;
    while accept p COMMA do
      skip_nl p;
      if peek p <> RPAREN then (args := parse_one () :: !args; skip_nl p)
    done
  end;
  eat p RPAREN;
  let args = List.rev !args in
  let has_rest = List.exists (function `Rest -> true | _ -> false) args in
  let has_named = List.exists (function `Named _ -> true | _ -> false) args in
  if has_rest || has_named then
    let fields =
      List.filter_map
        (function
          | `Rest -> None
          | `Named (name, pat) -> Some { rf_name = name; rf_pat = Some pat }
          | `Pat (PBind name) -> Some { rf_name = name; rf_pat = None }
          | `Pat _ -> err p "a record pattern field must be a bare name")
        args
    in
    CPRecord (fields, has_rest)
  else CPPos (List.map (function `Pat pat -> pat | _ -> assert false) args)

and parse_block p =
  eat p LBRACE;
  parse_block_body p

(* parse statements + optional trailing value up to and including `}` (assumes `{` consumed) *)
and parse_block_body p =
  let stmts = ref [] in
  let result = ref None in
  let continue = ref true in
  skip_nl p;
  while !continue && peek p <> RBRACE do
    (match peek p with
     | VAL | VAR -> stmts := parse_let p :: !stmts
     | RETURN ->
       ignore (advance p);
       let e =
         match peek p with NEWLINE | SEMI | RBRACE -> None | _ -> Some (parse_expr p 0)
       in
       stmts := SReturn e :: !stmts
     | WHILE -> stmts := parse_while p :: !stmts
     | FOR -> stmts := parse_for p :: !stmts
     | BREAK -> ignore (advance p); stmts := SBreak :: !stmts
     | CONTINUE -> ignore (advance p); stmts := SContinue :: !stmts
     | _ ->
       let e = parse_expr p 0 in
       if accept p ASSIGN then begin
         let rhs = parse_expr p 0 in
         stmts := SAssign (e, rhs) :: !stmts
       end
       else begin
         skip_nl p;
         if peek p = RBRACE then begin
           result := Some e;
           continue := false
         end
         else stmts := SExpr e :: !stmts
       end);
    skip_nl p
  done;
  eat p RBRACE;
  Block (List.rev !stmts, !result)

(* try to parse a leading `param (, param)* ->` (or `->`); pure lookahead —
   returns Some params (consuming the arrow) or None (restoring position). *)
and try_lambda_params p =
  let saved = p.idx in
  if peek p = ARROW then (ignore (advance p); Some [])
  else begin
    let params = ref [] in
    let ok =
      try
        let one () =
          match peek p with
          | IDENT s ->
            ignore (advance p);
            let ty = if accept p COLON then Some (parse_type p) else None in
            { lp_name = s; lp_ty = ty }
          | _ -> raise Exit
        in
        params := [ one () ];
        while accept p COMMA do params := one () :: !params done;
        peek p = ARROW
      with _ -> false
    in
    if ok then (ignore (advance p); Some (List.rev !params))
    else (p.idx <- saved; None)
  end

(* a `{ ... }` known to be a lambda (trailing-lambda position): implicit `it` if no params *)
and parse_trailing_lambda p =
  eat p LBRACE;
  skip_nl p;
  let params = match try_lambda_params p with Some ps -> ps | None -> [] in
  Lambda (params, parse_block_body p)

and parse_let p =
  let is_var = peek p = VAR in
  (match peek p with VAL | VAR -> ignore (advance p) | _ -> err p "expected val or var");
  let name = ident p in
  let ty = if accept p COLON then Some (parse_type p) else None in
  eat p ASSIGN;
  let init = parse_expr p 0 in
  SLet { name; ty; init; is_var }

and parse_while p =
  eat p WHILE;
  eat p LPAREN;
  let cond = parse_expr p 0 in
  eat p RPAREN;
  skip_nl p;
  let body = parse_block p in
  SWhile (cond, body)

and parse_for p =
  eat p FOR;
  eat p LPAREN;
  let var = ident p in
  eat p IN;
  let iter = parse_expr p 0 in
  eat p RPAREN;
  skip_nl p;
  let body = parse_block p in
  SFor { var; iter; body }

(* ---- declarations ---- *)

(* <T: Bound + Bound, U = Default> *)
let parse_generics p =
  if peek p <> LT then []
  else begin
    eat p LT;
    let one () =
      let gp_name = ident p in
      let gp_bounds =
        if accept p COLON then begin
          let bs = ref [ parse_type p ] in
          while accept p PLUS do bs := parse_type p :: !bs done;
          List.rev !bs
        end
        else []
      in
      let gp_default = if accept p ASSIGN then Some (parse_type p) else None in
      { gp_name; gp_bounds; gp_default }
    in
    let ps = ref [ one () ] in
    while accept p COMMA do ps := one () :: !ps done;
    eat p GT;
    List.rev !ps
  end

(* where T: A + B, U: C *)
let parse_where p =
  if not (accept p WHERE) then []
  else begin
    let one () =
      let t = parse_type p in
      eat p COLON;
      let bs = ref [ parse_type p ] in
      while accept p PLUS do bs := parse_type p :: !bs done;
      (t, List.rev !bs)
    in
    let cs = ref [ one () ] in
    while accept p COMMA do cs := one () :: !cs done;
    List.rev !cs
  end

(* `name: [inout|consuming] Type` *)
let parse_param p =
  let pname = ident p in
  eat p COLON;
  let pmode =
    match peek p with
    | INOUT -> ignore (advance p); PMInout
    | CONSUMING -> ignore (advance p); PMConsuming
    | _ -> PMNormal
  in
  let pty = parse_type p in
  { pname; pmode; pty }

let parse_receiver_opt p =
  match peek p with
  | SELF -> ignore (advance p); Some RSelf
  | MUT when peek_at p 1 = SELF -> ignore (advance p); ignore (advance p); Some RMutSelf
  | CONSUMING when peek_at p 1 = SELF -> ignore (advance p); ignore (advance p); Some RConsumingSelf
  | _ -> None

(* @name(args) annotations preceding a declaration *)
let parse_annotations p =
  let annos = ref [] in
  while peek p = AT do
    ignore (advance p);
    let an_name = ident p in
    let an_args =
      if peek p = LPAREN then begin
        ignore (advance p);
        skip_nl p;
        let args = ref [] in
        if peek p <> RPAREN then begin
          args := [ parse_expr p 0 ];
          skip_nl p;
          while accept p COMMA do
            skip_nl p;
            if peek p <> RPAREN then (args := parse_expr p 0 :: !args; skip_nl p)
          done
        end;
        eat p RPAREN;
        List.rev !args
      end
      else []
    in
    annos := { an_name; an_args } :: !annos;
    skip_nl p
  done;
  List.rev !annos

let parse_fun ?(annos = []) p =
  eat p FUN;
  let g1 = parse_generics p in       (* free fn: fun <T> name(...) *)
  let fn_name = ident p in
  let fn_generics = if g1 = [] then parse_generics p else g1 in  (* method: fun name<T>(...) *)
  eat p LPAREN;
  skip_nl p;
  let fn_receiver = parse_receiver_opt p in
  let fn_params = ref [] in
  let need_more =
    if fn_receiver <> None then (skip_nl p; accept p COMMA)
    else peek p <> RPAREN
  in
  if need_more then begin
    skip_nl p;
    fn_params := [ parse_param p ];
    skip_nl p;
    while accept p COMMA do
      skip_nl p;
      if peek p <> RPAREN then (fn_params := parse_param p :: !fn_params; skip_nl p)
    done
  end;
  eat p RPAREN;
  let fn_ret = if accept p COLON then Some (parse_type p) else None in
  let fn_where = parse_where p in
  skip_nl p;
  let fn_body =
    match peek p with
    | ASSIGN -> ignore (advance p); Some (parse_expr p 0)
    | LBRACE -> Some (parse_block p)
    | _ -> None (* signature only (trait method sig) *)
  in
  {
    fn_annos = annos;
    fn_name;
    fn_generics;
    fn_receiver;
    fn_params = List.rev !fn_params;
    fn_ret;
    fn_where;
    fn_body;
  }

(* `[pub] (val|var) name: Type` — a primary-constructor field *)
let parse_ctor_field p =
  let cf_pub = accept p PUB in
  let cf_mut =
    match peek p with
    | VAL -> ignore (advance p); false
    | VAR -> ignore (advance p); true
    | _ -> err p "expected val or var"
  in
  let cf_name = ident p in
  eat p COLON;
  let cf_ty = parse_type p in
  { cf_pub; cf_mut; cf_name; cf_ty }

(* `name: Type` — an enum variant's named field (no pub/val/var) *)
let parse_named_field p =
  let cf_name = ident p in
  eat p COLON;
  let cf_ty = parse_type p in
  { cf_pub = false; cf_mut = false; cf_name; cf_ty }

(* `( field, field, ... )` — assumes the current token is LPAREN *)
let parse_ctor_fields p =
  eat p LPAREN;
  skip_nl p;
  let fields = ref [] in
  if peek p <> RPAREN then begin
    fields := [ parse_ctor_field p ];
    skip_nl p;
    while accept p COMMA do
      skip_nl p;
      fields := parse_ctor_field p :: !fields;
      skip_nl p
    done
  end;
  eat p RPAREN;
  List.rev !fields

(* optional brace body; for now it holds at most a single `deinit { ... }`
   (inherent methods live in impl blocks — a later increment) *)
let parse_type_body p =
  if peek p <> LBRACE then ([], None)
  else begin
    eat p LBRACE;
    skip_nl p;
    let methods = ref [] in
    let deinit = ref None in
    while peek p <> RBRACE do
      let annos = parse_annotations p in
      (match peek p with
       | DEINIT -> ignore (advance p); skip_nl p; deinit := Some (parse_block p)
       | FUN -> methods := parse_fun ~annos p :: !methods
       | _ -> err p "expected a method (`fun`) or `deinit` in the type body");
      skip_nl p
    done;
    eat p RBRACE;
    (List.rev !methods, !deinit)
  end

let parse_struct_or_class ?(annos = []) p ~is_class =
  ignore (advance p); (* STRUCT or CLASS *)
  let td_name = ident p in
  let td_generics = parse_generics p in
  skip_nl p;
  let td_fields = if peek p = LPAREN then parse_ctor_fields p else [] in
  skip_nl p;
  let td_where = parse_where p in
  skip_nl p;
  let td_methods, td_deinit = parse_type_body p in
  let td =
    { td_annos = annos; td_name; td_generics; td_fields; td_where; td_deinit; td_methods }
  in
  if is_class then ClassDecl td else StructDecl td

(* one enum variant: `Name`, `Name(Type, ...)`, or `Name(field: Type, ...)` *)
let parse_variant p =
  let var_name = ident p in
  let var_payload =
    if peek p <> LPAREN then PNone
    else begin
      eat p LPAREN;
      skip_nl p;
      if peek p = RPAREN then (ignore (advance p); PNone)
      else begin
        (* named payload iff it starts with pub/val/var or `ident :` *)
        let named =
          match peek p with IDENT _ -> peek_at p 1 = COLON | _ -> false
        in
        if named then begin
          let fields = ref [ parse_named_field p ] in
          skip_nl p;
          while accept p COMMA do
            skip_nl p;
            fields := parse_named_field p :: !fields;
            skip_nl p
          done;
          eat p RPAREN;
          PNamed (List.rev !fields)
        end
        else begin
          let tys = ref [ parse_type p ] in
          skip_nl p;
          while accept p COMMA do
            skip_nl p;
            tys := parse_type p :: !tys;
            skip_nl p
          done;
          eat p RPAREN;
          PPositional (List.rev !tys)
        end
      end
    end
  in
  { var_name; var_payload }

let parse_enum ?(annos = []) p =
  eat p ENUM;
  let ed_name = ident p in
  let ed_generics = parse_generics p in
  skip_nl p;
  eat p LBRACE;
  skip_nl p;
  let variants = ref [] in
  while peek p <> RBRACE do
    variants := parse_variant p :: !variants;
    skip_nl p
  done;
  eat p RBRACE;
  EnumDecl { ed_annos = annos; ed_name; ed_generics; ed_variants = List.rev !variants }

(* trait/impl bodies share the same member grammar: `type` assoc + `fun` methods *)
let parse_trait ?(annos = []) p =
  eat p TRAIT;
  let tr_name = ident p in
  let tr_generics = parse_generics p in
  let tr_supers =
    if accept p COLON then begin
      let bs = ref [ parse_type p ] in
      while accept p PLUS do bs := parse_type p :: !bs done;
      List.rev !bs
    end
    else []
  in
  let tr_where = parse_where p in
  skip_nl p;
  eat p LBRACE;
  skip_nl p;
  let assoc = ref [] in
  let methods = ref [] in
  while peek p <> RBRACE do
    let m_annos = parse_annotations p in
    (match peek p with
     | IDENT "type" ->
       ignore (advance p);
       let name = ident p in
       let bounds =
         if accept p COLON then begin
           let bs = ref [ parse_type p ] in
           while accept p PLUS do bs := parse_type p :: !bs done;
           List.rev !bs
         end
         else []
       in
       assoc := (name, bounds) :: !assoc
     | FUN -> methods := parse_fun ~annos:m_annos p :: !methods
     | _ -> err p "expected `type` or `fun` in trait body");
    skip_nl p
  done;
  eat p RBRACE;
  TraitDecl
    {
      tr_annos = annos;
      tr_name;
      tr_generics;
      tr_supers;
      tr_where;
      tr_assoc = List.rev !assoc;
      tr_methods = List.rev !methods;
    }

let parse_impl ?(annos = []) p =
  eat p IMPL;
  let im_generics = parse_generics p in
  let first = parse_type p in
  let im_trait, im_type =
    if accept p FOR then
      match first with
      | TyPath (path, args) -> (Some (path, args), parse_type p)
      | _ -> err p "expected a trait name before `for`"
    else (None, first)
  in
  let im_where = parse_where p in
  skip_nl p;
  eat p LBRACE;
  skip_nl p;
  let assoc = ref [] in
  let methods = ref [] in
  while peek p <> RBRACE do
    let m_annos = parse_annotations p in
    (match peek p with
     | IDENT "type" ->
       ignore (advance p);
       let name = ident p in
       eat p ASSIGN;
       assoc := (name, parse_type p) :: !assoc
     | FUN -> methods := parse_fun ~annos:m_annos p :: !methods
     | _ -> err p "expected `type` or `fun` in impl body");
    skip_nl p
  done;
  eat p RBRACE;
  ImplDecl
    {
      im_annos = annos;
      im_generics;
      im_trait;
      im_type;
      im_where;
      im_assoc = List.rev !assoc;
      im_methods = List.rev !methods;
    }

let parse_import p =
  eat p IMPORT;
  let path = ref [ ident p ] in
  while accept p COLONCOLON do
    path := ident p :: !path
  done;
  Import (List.rev !path)

let parse_decl p =
  let annos = parse_annotations p in
  match peek p with
  | IMPORT -> parse_import p
  | STRUCT -> parse_struct_or_class ~annos p ~is_class:false
  | CLASS -> parse_struct_or_class ~annos p ~is_class:true
  | ENUM -> parse_enum ~annos p
  | TRAIT -> parse_trait ~annos p
  | IMPL -> parse_impl ~annos p
  | FUN -> FunDecl (parse_fun ~annos p)
  | _ -> err p "expected a top-level declaration (import, struct, class, enum, trait, impl, or fun)"

let parse_program (toks : Token.located list) : program =
  let p = make toks in
  let decls = ref [] in
  skip_nl p;
  while peek p <> EOF do
    decls := parse_decl p :: !decls;
    skip_nl p
  done;
  List.rev !decls
