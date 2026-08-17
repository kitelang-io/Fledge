(* M2, pass 1 — name resolution.

   Builds a table of top-level names (functions, types, enum variants, traits),
   flags duplicate top-level definitions, then walks every function/method body
   tracking a lexical scope stack and flags value identifiers that resolve to
   nothing (not a local, not a top-level name, not a seeded prelude builtin).

   NOTE: the AST currently carries no source spans, so diagnostics are
   position-free for now (adding spans is a planned M2 refinement). Only
   *value* identifiers are resolved here; type names are checked in the type
   checker (a later M2 pass). *)

open Ast

module SS = Set.Make (String)

(* seeded prelude / builtin value names, expanded as the stdlib grows.
   The second row mirrors the intrinsics the backend actually lowers
   (codegen_arm64.ml) — keep the two in sync so `check` does not flag
   names that `run` compiles. *)
let builtins =
  SS.of_list
    [ "println"; "print"; "eprintln"; "eprint";
      "assert"; "panic"; "abort"; "todo"; "unreachable";
      "unit"; "it";
      "Some"; "None"; "Ok"; "Err";
      "string"; "listOf"; "mapOf"; "setOf";
      "list"; "map"; "toInt"; "comptime"; "__argv";
      (* backend-implemented value builtins (Fledge stage-0 intrinsics) *)
      "strLen"; "charAt"; "strEq"; "concat"; "substr"; "intToStr";
      "listNew"; "listPush"; "listGet"; "listSet"; "listLen"; "readFile"; "writeFile";
      "fopenW"; "fputByte"; "fcloseF";
      (* ARC + raw-memory + map intrinsics (mirror kcheck.kite's isBuiltin;
         __argv/list/map/toInt/comptime are already listed above) *)
      "__retain"; "__release"; "__refcount"; "__decRefcount"; "__freeObj"; "__allocRC"; "__typeId";
      "__rawAlloc"; "__rawFree"; "__rawRealloc"; "__rawLoad"; "__rawStore"; "__rawLoadByte"; "__rawStoreByte";
      "__mapGetS"; "__mapGetI" ]

type ctx = {
  globals : SS.t;
  mutable scopes : SS.t list;
  diags : string list ref;
}

let err ctx msg = ctx.diags := msg :: !(ctx.diags)

let is_bound ctx name =
  List.exists (SS.mem name) ctx.scopes
  || SS.mem name ctx.globals
  || SS.mem name builtins

let bind ctx name =
  match ctx.scopes with
  | s :: rest -> ctx.scopes <- SS.add name s :: rest
  | [] -> ctx.scopes <- [ SS.singleton name ]

let with_scope ctx f =
  ctx.scopes <- SS.empty :: ctx.scopes;
  let r = f () in
  ctx.scopes <- (match ctx.scopes with _ :: t -> t | [] -> []);
  r

let rec r_expr ctx e =
  match e with
  | IntLit _ | FloatLit _ | StringLit _ | CharLit _ | BoolLit _ | NullLit | This
  | EBreak | EContinue -> ()
  | Ident s -> if not (is_bound ctx s) then err ctx (Printf.sprintf "unresolved name: %s" s)
  | Unary (_, a) | NotNull a | Field (a, _) | SafeField (a, _) | Static (a, _)
  | TypeApp (a, _) -> r_expr ctx a
  | Binary (_, a, b) | Elvis (a, b) | Index (a, b) -> r_expr ctx a; r_expr ctx b
  | Call (f, args) -> r_expr ctx f; List.iter (fun a -> r_expr ctx a.arg_val) args
  | ListLit es -> List.iter (r_expr ctx) es
  | MapLit kvs -> List.iter (fun (k, v) -> r_expr ctx k; r_expr ctx v) kvs
  | Interp parts -> List.iter (function ILit _ -> () | IExpr e -> r_expr ctx e) parts
  | EReturn eo -> Option.iter (r_expr ctx) eo
  | If (c, t, eo) -> r_expr ctx c; r_expr ctx t; Option.iter (r_expr ctx) eo
  | Lambda (params, body) ->
    with_scope ctx (fun () ->
        List.iter (fun lp -> bind ctx lp.lp_name) params;
        r_expr ctx body)
  | Block (stmts, result) ->
    with_scope ctx (fun () ->
        List.iter (r_stmt ctx) stmts;
        Option.iter (r_expr ctx) result)
  | When (subject, arms) ->
    Option.iter (fun s -> r_expr ctx s.ws_expr) subject;
    List.iter
      (fun arm ->
        with_scope ctx (fun () ->
            Option.iter (fun s -> Option.iter (bind ctx) s.ws_bind) subject;
            (match arm.wa_lhs with
             | LhsElse -> ()
             | LhsCond c -> r_expr ctx c
             | LhsPatterns pats -> List.iter (r_pattern ctx) pats);
            Option.iter (r_expr ctx) arm.wa_guard;
            r_expr ctx arm.wa_body))
      arms

and r_stmt ctx s =
  match s with
  | SLet { name; init; _ } -> r_expr ctx init; bind ctx name
  | SExpr e -> r_expr ctx e
  | SAssign (l, r) -> r_expr ctx l; r_expr ctx r
  | SReturn eo -> Option.iter (r_expr ctx) eo
  | SWhile (c, b) -> r_expr ctx c; r_expr ctx b
  | SFor { var; iter; body } ->
    r_expr ctx iter;
    with_scope ctx (fun () -> bind ctx var; r_expr ctx body)
  | SBreak | SContinue -> ()

(* patterns bind their variables into the current (already-pushed) scope *)
and r_pattern ctx pat =
  match pat with
  | PWild | PLitInt _ | PLitFloat _ | PLitString _ | PLitChar _ | PLitBool _
  | PLitNull | PPath _ | PIs _ -> ()
  | PBind s -> bind ctx s
  | PIn (e, _) -> r_expr ctx e
  | PCtor (_, CPPos pats) -> List.iter (r_pattern ctx) pats
  | PCtor (_, CPRecord (fields, _)) ->
    List.iter
      (fun f -> match f.rf_pat with Some p -> r_pattern ctx p | None -> bind ctx f.rf_name)
      fields

let r_fun ctx fd =
  match fd.fn_body with
  | None -> () (* trait signature — nothing to resolve *)
  | Some body ->
    with_scope ctx (fun () ->
        List.iter (fun pr -> bind ctx pr.pname) fd.fn_params;
        r_expr ctx body)

let r_decl ctx d =
  match d with
  | Import _ -> ()
  | FunDecl fd -> r_fun ctx fd
  | StructDecl td | ClassDecl td ->
    Option.iter (fun e -> with_scope ctx (fun () -> r_expr ctx e)) td.td_deinit;
    List.iter (r_fun ctx) td.td_methods
  | EnumDecl _ -> ()
  | TraitDecl tr -> List.iter (r_fun ctx) tr.tr_methods
  | ImplDecl im -> List.iter (r_fun ctx) im.im_methods

let check (prog : program) : string list =
  let diags = ref [] in
  let seen = Hashtbl.create 64 in
  let globals = ref SS.empty in
  let add_global n = globals := SS.add n !globals in
  let define n =
    if Hashtbl.mem seen n then
      diags := Printf.sprintf "duplicate top-level definition: %s" n :: !diags;
    Hashtbl.replace seen n ();
    add_global n
  in
  List.iter
    (fun d ->
      match d with
      | FunDecl fd -> define fd.fn_name
      | StructDecl td | ClassDecl td -> define td.td_name
      | EnumDecl ed ->
        define ed.ed_name;
        List.iter (fun v -> add_global v.var_name) ed.ed_variants
      | TraitDecl tr -> define tr.tr_name
      | ImplDecl _ | Import _ -> ())
    prog;
  let ctx = { globals = !globals; scopes = []; diags } in
  List.iter (r_decl ctx) prog;
  List.rev !diags
