(* Indentation-based pretty-printer for the AST — used by `kitec parse` to make
   the parse result easy to eyeball. *)

open Ast

let spf = Printf.sprintf

let string_of_unop = function Neg -> "neg -" | Not -> "not !"

let string_of_binop = function
  | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
  | Eq -> "==" | Neq -> "!=" | Lt -> "<" | Gt -> ">" | Le -> "<=" | Ge -> ">="
  | And -> "&&" | Or -> "||"
  | BAnd -> "&" | BOr -> "|" | BXor -> "^" | Shl -> "<<" | Shr -> ">>"
  | Range -> ".."

let rec string_of_ty = function
  | TyPath (path, []) -> String.concat "::" path
  | TyPath (path, args) ->
    String.concat "::" path ^ "<" ^ String.concat ", " (List.map string_of_ty args) ^ ">"
  | TyNullable t -> string_of_ty t ^ "?"
  | TyFun (args, ret) ->
    "(" ^ String.concat ", " (List.map string_of_ty args) ^ ") -> " ^ string_of_ty ret

let program_to_string (prog : program) : string =
  let buf = Buffer.create 512 in
  let line ind s =
    for _ = 1 to ind do Buffer.add_string buf "  " done;
    Buffer.add_string buf s;
    Buffer.add_char buf '\n'
  in
  let rec pe ind e =
    match e with
    | IntLit n -> line ind (spf "int %d" n)
    | FloatLit f -> line ind (spf "float %g" f)
    | StringLit s -> line ind (spf "string %S" s)
    | CharLit c -> line ind (spf "char %d" c)
    | BoolLit b -> line ind (spf "bool %b" b)
    | NullLit -> line ind "null"
    | This -> line ind "this"
    | Ident s -> line ind (spf "ident %s" s)
    | Unary (op, e) -> line ind (spf "unary %s" (string_of_unop op)); pe (ind + 1) e
    | Binary (op, l, r) ->
      line ind (spf "binary %s" (string_of_binop op));
      pe (ind + 1) l;
      pe (ind + 1) r
    | Elvis (a, b) -> line ind "elvis ?:"; pe (ind + 1) a; pe (ind + 1) b
    | NotNull e -> line ind "not-null !!"; pe (ind + 1) e
    | Field (e, n) -> line ind (spf "field .%s" n); pe (ind + 1) e
    | SafeField (e, n) -> line ind (spf "safe-field ?.%s" n); pe (ind + 1) e
    | Static (e, n) -> line ind (spf "static ::%s" n); pe (ind + 1) e
    | Call (f, args) ->
      line ind "call";
      pe (ind + 1) f;
      if args <> [] then begin
        line (ind + 1) "args";
        List.iter
          (fun { arg_name; arg_val } ->
            match arg_name with
            | Some n -> line (ind + 2) (spf "%s =" n); pe (ind + 3) arg_val
            | None -> pe (ind + 2) arg_val)
          args
      end
    | Index (e, i) -> line ind "index"; pe (ind + 1) e; pe (ind + 1) i
    | TypeApp (e, tys) ->
      line ind (spf "type-app ::<%s>" (String.concat ", " (List.map string_of_ty tys)));
      pe (ind + 1) e
    | ListLit es -> line ind "list"; List.iter (pe (ind + 1)) es
    | MapLit kvs ->
      line ind "map";
      List.iter (fun (k, v) -> line (ind + 1) "entry"; pe (ind + 2) k; pe (ind + 2) v) kvs
    | Lambda (params, body) ->
      let ps =
        String.concat ", "
          (List.map
             (fun { lp_name; lp_ty } ->
               match lp_ty with Some t -> lp_name ^ ": " ^ string_of_ty t | None -> lp_name)
             params)
      in
      line ind (spf "lambda (%s)" ps);
      pe (ind + 1) body
    | If (c, t, e) ->
      line ind "if";
      pe (ind + 1) c;
      line (ind + 1) "then"; pe (ind + 2) t;
      (match e with Some x -> line (ind + 1) "else"; pe (ind + 2) x | None -> ())
    | When (subject, arms) ->
      line ind "when";
      (match subject with
       | Some { ws_bind; ws_consuming; ws_expr } ->
         let b = match ws_bind with Some n -> "val " ^ n ^ " = " | None -> "" in
         let c = if ws_consuming then "consuming " else "" in
         line (ind + 1) (spf "subject %s%s" b c);
         pe (ind + 2) ws_expr
       | None -> ());
      List.iter
        (fun { wa_lhs; wa_guard; wa_body } ->
          (match wa_lhs with
           | LhsElse -> line (ind + 1) "else"
           | LhsCond e -> line (ind + 1) "cond"; pe (ind + 2) e
           | LhsPatterns pats -> line (ind + 1) "patterns"; List.iter (pp (ind + 2)) pats);
          (match wa_guard with Some g -> line (ind + 1) "guard"; pe (ind + 2) g | None -> ());
          line (ind + 1) "->";
          pe (ind + 2) wa_body)
        arms
    | Block (stmts, res) ->
      line ind "block";
      List.iter (ps (ind + 1)) stmts;
      (match res with Some e -> line (ind + 1) "result"; pe (ind + 2) e | None -> ())
    | Interp parts ->
      line ind "interp";
      List.iter
        (fun part ->
          match part with
          | ILit s -> line (ind + 1) (spf "lit %S" s)
          | IExpr e -> line (ind + 1) "expr"; pe (ind + 2) e)
        parts
    | EReturn None -> line ind "return"
    | EReturn (Some e) -> line ind "return"; pe (ind + 1) e
    | EBreak -> line ind "break"
    | EContinue -> line ind "continue"
  and ps ind s =
    match s with
    | SLet { name; ty; init; is_var } ->
      let kw = if is_var then "var" else "val" in
      let tystr = match ty with Some t -> " : " ^ string_of_ty t | None -> "" in
      line ind (spf "%s %s%s" kw name tystr);
      pe (ind + 1) init
    | SExpr e -> line ind "expr-stmt"; pe (ind + 1) e
    | SAssign (l, r) -> line ind "assign ="; pe (ind + 1) l; pe (ind + 1) r
    | SReturn None -> line ind "return"
    | SReturn (Some e) -> line ind "return"; pe (ind + 1) e
    | SWhile (c, b) -> line ind "while"; pe (ind + 1) c; pe (ind + 1) b
    | SFor { var; iter; body } ->
      line ind (spf "for %s in" var); pe (ind + 1) iter; pe (ind + 1) body
    | SBreak -> line ind "break"
    | SContinue -> line ind "continue"
  and pp ind pat =
    match pat with
    | PWild -> line ind "_"
    | PBind s -> line ind (spf "bind %s" s)
    | PLitInt n -> line ind (spf "int %d" n)
    | PLitFloat f -> line ind (spf "float %g" f)
    | PLitString s -> line ind (spf "string %S" s)
    | PLitChar c -> line ind (spf "char %d" c)
    | PLitBool b -> line ind (spf "bool %b" b)
    | PLitNull -> line ind "null"
    | PPath path -> line ind (spf "variant %s" (String.concat "::" path))
    | PCtor (path, args) ->
      line ind (spf "ctor %s" (String.concat "::" path));
      (match args with
       | CPPos pats -> List.iter (pp (ind + 1)) pats
       | CPRecord (fs, rest) ->
         List.iter
           (fun { rf_name; rf_pat } ->
             match rf_pat with
             | None -> line (ind + 1) (spf "field %s (pun)" rf_name)
             | Some p -> line (ind + 1) (spf "field %s =" rf_name); pp (ind + 2) p)
           fs;
         if rest then line (ind + 1) "..")
    | PIs (t, neg) -> line ind (spf "%sis %s" (if neg then "!" else "") (string_of_ty t))
    | PIn (e, neg) -> line ind (spf "%sin" (if neg then "!" else "")); pe (ind + 1) e
  in
  let bounds_str bs = if bs = [] then "" else String.concat " + " (List.map string_of_ty bs) in
  let string_of_generics gs =
    if gs = [] then ""
    else
      "<"
      ^ String.concat ", "
          (List.map
             (fun { gp_name; gp_bounds; gp_default } ->
               gp_name
               ^ (if gp_bounds = [] then "" else ": " ^ bounds_str gp_bounds)
               ^ (match gp_default with Some t -> " = " ^ string_of_ty t | None -> ""))
             gs)
      ^ ">"
  in
  let string_of_where w =
    if w = [] then ""
    else
      " where "
      ^ String.concat ", " (List.map (fun (t, bs) -> string_of_ty t ^ ": " ^ bounds_str bs) w)
  in
  let string_of_pmode = function PMNormal -> "" | PMInout -> "inout " | PMConsuming -> "consuming " in
  let string_of_param { pname; pmode; pty } = spf "%s: %s%s" pname (string_of_pmode pmode) (string_of_ty pty) in
  let string_of_recv = function
    | RSelf -> "self" | RMutSelf -> "mut self" | RConsumingSelf -> "consuming self"
  in
  let string_of_field { cf_pub; cf_mut; cf_name; cf_ty } =
    spf "%s%s %s : %s" (if cf_pub then "pub " else "") (if cf_mut then "var" else "val") cf_name (string_of_ty cf_ty)
  in
  let panno ind { an_name; an_args } =
    if an_args = [] then line ind (spf "@%s" an_name)
    else (line ind (spf "@%s(...)" an_name); List.iter (pe (ind + 1)) an_args)
  in
  let pfun ind fd =
    List.iter (panno ind) fd.fn_annos;
    let recv =
      match fd.fn_receiver with
      | Some r -> string_of_recv r ^ (if fd.fn_params = [] then "" else ", ")
      | None -> ""
    in
    let ps_ = String.concat ", " (List.map string_of_param fd.fn_params) in
    let rets = match fd.fn_ret with Some t -> " : " ^ string_of_ty t | None -> "" in
    line ind
      (spf "fun %s%s(%s%s)%s%s" fd.fn_name (string_of_generics fd.fn_generics) recv ps_ rets
         (string_of_where fd.fn_where));
    match fd.fn_body with Some e -> pe (ind + 1) e | None -> line (ind + 1) "(signature)"
  in
  let ptd kind td =
    List.iter (panno 0) td.td_annos;
    line 0 (spf "%s %s%s%s" kind td.td_name (string_of_generics td.td_generics) (string_of_where td.td_where));
    List.iter (fun f -> line 1 (string_of_field f)) td.td_fields;
    (match td.td_deinit with Some e -> line 1 "deinit"; pe 2 e | None -> ());
    List.iter (pfun 1) td.td_methods
  in
  let pd d =
    match d with
    | Import path -> line 0 (spf "import %s" (String.concat "::" path))
    | FunDecl fd -> pfun 0 fd
    | StructDecl td -> ptd "struct" td
    | ClassDecl td -> ptd "class" td
    | EnumDecl { ed_annos; ed_name; ed_generics; ed_variants } ->
      List.iter (panno 0) ed_annos;
      line 0 (spf "enum %s%s" ed_name (string_of_generics ed_generics));
      List.iter
        (fun { var_name; var_payload } ->
          match var_payload with
          | PNone -> line 1 var_name
          | PPositional tys ->
            line 1 (spf "%s(%s)" var_name (String.concat ", " (List.map string_of_ty tys)))
          | PNamed fs ->
            line 1 (spf "%s(%s)" var_name (String.concat ", " (List.map string_of_field fs))))
        ed_variants
    | TraitDecl tr ->
      List.iter (panno 0) tr.tr_annos;
      let supers = if tr.tr_supers = [] then "" else " : " ^ bounds_str tr.tr_supers in
      line 0
        (spf "trait %s%s%s%s" tr.tr_name (string_of_generics tr.tr_generics) supers
           (string_of_where tr.tr_where));
      List.iter
        (fun (n, bs) -> line 1 (spf "type %s%s" n (if bs = [] then "" else " : " ^ bounds_str bs)))
        tr.tr_assoc;
      List.iter (pfun 1) tr.tr_methods
    | ImplDecl im ->
      List.iter (panno 0) im.im_annos;
      let head =
        match im.im_trait with
        | Some (path, args) ->
          let tr =
            String.concat "::" path
            ^ (if args = [] then "" else "<" ^ String.concat ", " (List.map string_of_ty args) ^ ">")
          in
          spf "impl%s %s for %s%s" (string_of_generics im.im_generics) tr (string_of_ty im.im_type)
            (string_of_where im.im_where)
        | None ->
          spf "impl%s %s%s" (string_of_generics im.im_generics) (string_of_ty im.im_type)
            (string_of_where im.im_where)
      in
      line 0 head;
      List.iter (fun (n, t) -> line 1 (spf "type %s = %s" n (string_of_ty t))) im.im_assoc;
      List.iter (pfun 1) im.im_methods
  in
  List.iter (fun d -> pd d; Buffer.add_char buf '\n') prog;
  Buffer.contents buf
