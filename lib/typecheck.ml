(* M2, pass 2 — a first, deliberately lenient type checker.

   It infers a checker-internal type for every expression and reports ONLY
   definite mismatches (arithmetic on non-numerics, wrong call arity, a non-Bool
   `if` condition, an annotation/return incompatible with its value, assigning a
   nullable to a non-null slot, unknown field access on a known struct). Anything
   it cannot yet reason about (generic/trait method calls, enum-variant
   construction, stdlib names) becomes `TUnknown`, which is compatible with
   everything — so the pass never false-positives on constructs later passes will
   handle. Diagnostics are position-free for now (the AST carries no spans yet). *)

open Ast

type ty =
  | TPrim of string           (* Int, Long, Bool, Float, Double, String, Char, Unit, Nothing, ... *)
  | TNamed of string * ty list
  | TNull of ty               (* T? *)
  | TFun of ty list * ty
  | TUnknown

let primitives =
  [ "Int"; "Long"; "Bool"; "Float"; "Double"; "String"; "Char"; "Unit"; "Nothing";
    "Int8"; "Int16"; "Int32"; "Int64"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "ISize"; "USize" ]

let numeric =
  [ "Int"; "Long"; "Float"; "Double";
    "Int8"; "Int16"; "Int32"; "Int64"; "UInt8"; "UInt16"; "UInt32"; "UInt64"; "ISize"; "USize" ]

let is_numeric = function TPrim x -> List.mem x numeric | _ -> false

(* convert a surface type to a checker type; a non-primitive path/type-param
   becomes TNamed of its last segment (generics stay opaque but name-comparable) *)
let rec of_ast (t : Ast.ty) : ty =
  match t with
  | TyPath (path, args) ->
    let name = List.nth path (List.length path - 1) in
    if List.mem name primitives && args = [] then TPrim name
    else TNamed (name, List.map of_ast args)
  | TyNullable t -> TNull (of_ast t)
  | TyFun (args, ret) -> TFun (List.map of_ast args, of_ast ret)

let rec compat a b =
  match a, b with
  | TUnknown, _ | _, TUnknown -> true
  | TPrim "Nothing", _ | _, TPrim "Nothing" -> true
  | TPrim x, TPrim y -> x = y || (List.mem x numeric && List.mem y numeric)
  | TNull x, TNull y -> compat x y
  | a, TNull y -> compat a y          (* non-null value fits a nullable slot *)
  | TNull _, _ -> false               (* a nullable does NOT fit a non-null slot *)
  | TNamed (n1, a1), TNamed (n2, a2) ->
    n1 = n2 && List.length a1 = List.length a2 && List.for_all2 compat a1 a2
  | TFun (p1, r1), TFun (p2, r2) ->
    List.length p1 = List.length p2 && List.for_all2 compat p1 p2 && compat r1 r2
  | _ -> false

let join a b = if compat a b then b else if compat b a then a else TUnknown

(* a single uppercase letter (T, A, K, V, ...) is an erased generic type PARAMETER *)
let is_type_param n = String.length n = 1 && n.[0] >= 'A' && n.[0] <= 'Z'
let is_type_param_ty = function TNamed (n, _) -> is_type_param n | _ -> false
let is_unknown = function TUnknown -> true | _ -> false
(* a "concrete" type we can reason about for type-parameter binding consistency: a real primitive or a
   NON-type-parameter named type (a struct/enum/trait). *)
let rec is_concrete = function
  | TPrim _ -> true
  | TNamed (n, _) -> not (is_type_param n)
  | TNull x -> is_concrete x
  | _ -> false
let rec head_name = function TPrim x -> x | TNamed (n, _) -> n | TNull x -> head_name x | _ -> ""

let rec show = function
  | TPrim s -> s
  | TNamed (n, []) -> n
  | TNamed (n, args) -> n ^ "<" ^ String.concat ", " (List.map show args) ^ ">"
  | TNull t -> show t ^ "?"
  | TFun (ps, r) -> "(" ^ String.concat ", " (List.map show ps) ^ ") -> " ^ show r
  | TUnknown -> "?unknown"

type struct_info = { fields : (string * ty) list }

type env = {
  funs : (string, ty list * ty) Hashtbl.t;
  fun_gens : (string, generics) Hashtbl.t;      (* callee name -> generic params (for trait bounds) *)
  structs : (string, struct_info) Hashtbl.t;
  enums : (string, unit) Hashtbl.t;
  impls : (string * string) list ref;           (* (type name, trait name) from `impl Trait for Type` *)
  mutable locals : (string * ty) list list;
  mutable cur_ret : ty option;
  diags : string list ref;
}

let err env msg = env.diags := msg :: !(env.diags)

(* ---- generic instantiation (Target 1) ---- *)
(* Bind type parameter [n] to argument type [at] for THIS call (subst is per-call). The consistency
   error fires ONLY when the same parameter is bound twice to two mutually-incompatible CONCRETE types —
   a definite type error under any instantiation. Opaque bindings (Unknown / another type-parameter)
   are permissive and upgrade toward the concrete one, so no false positives on polymorphic code. *)
let bind_type_var env subst n at =
  match List.assoc_opt n !subst with
  | None -> subst := (n, at) :: !subst
  | Some prev ->
    if is_unknown prev || is_type_param_ty prev then subst := (n, at) :: List.remove_assoc n !subst
    else if is_unknown at || is_type_param_ty at then ()
    else if is_concrete prev && is_concrete at then
      (if (not (compat at prev)) && not (compat prev at) then
         err env (Printf.sprintf "type parameter %s bound to incompatible types %s and %s" n (show prev) (show at)))
    else ()

(* substitute bound type parameters into a (return) type *)
let rec inst_ty subst t =
  match t with
  | TNamed (n, []) when is_type_param n ->
    (match List.assoc_opt n !subst with Some b -> b | None -> t)
  | TNamed (n, args) -> TNamed (n, List.map (inst_ty subst) args)
  | TNull x -> TNull (inst_ty subst x)
  | TFun (ps, r) -> TFun (List.map (inst_ty subst) ps, inst_ty subst r)
  | _ -> t

(* ---- trait-bounds enforcement (Target 2) ---- *)
(* trait-bound names declared on generic parameter [n] (e.g. `<T: Show + Eq>` -> ["Show"; "Eq"]) *)
let bounds_of_generics generics n =
  match List.find_opt (fun gp -> gp.gp_name = n) generics with
  | Some gp -> List.map (fun b -> head_name (of_ast b)) gp.gp_bounds
  | None -> []
(* When type parameter [n: SomeTrait] is instantiated with a CONCRETE type [at], require that type to
   impl the trait (impl registry). Only concrete types are checked, so passing another type parameter
   through never false-positives. *)
let check_bound env generics n at =
  if is_concrete at then
    let cn = head_name at in
    List.iter
      (fun tr ->
        if not (List.mem (cn, tr) !(env.impls)) then
          err env (Printf.sprintf "type %s does not satisfy trait bound %s on type parameter %s" (show at) tr n))
      (bounds_of_generics generics n)

let lookup_local env name =
  let rec go = function
    | [] -> None
    | s :: rest -> (match List.assoc_opt name s with Some t -> Some t | None -> go rest)
  in
  go env.locals

let bind env name ty =
  match env.locals with
  | s :: rest -> env.locals <- ((name, ty) :: s) :: rest
  | [] -> env.locals <- [ [ (name, ty) ] ]

let with_scope env f =
  env.locals <- [] :: env.locals;
  let r = f () in
  env.locals <- (match env.locals with _ :: t -> t | [] -> []);
  r

let ret_of_named env name =
  if Hashtbl.mem env.structs name then Some (TNamed (name, []))
  else if Hashtbl.mem env.enums name then Some (TNamed (name, []))
  else None

let rec infer env e : ty =
  match e with
  | IntLit _ -> TPrim "Int"
  | FloatLit _ -> TPrim "Double"
  | StringLit _ | Interp _ -> TPrim "String"
  | CharLit _ -> TPrim "Char"
  | BoolLit _ -> TPrim "Bool"
  | NullLit -> TNull TUnknown
  | This -> TUnknown
  | EBreak | EContinue | EReturn _ -> TPrim "Nothing"
  | Ident s ->
    (match lookup_local env s with
     | Some t -> t
     | None ->
       (match Hashtbl.find_opt env.funs s with
        | Some (ps, r) -> TFun (ps, r)
        | None ->
          (match Hashtbl.find_opt env.structs s with
           | Some si -> TFun (List.map snd si.fields, TNamed (s, []))
           | None -> TUnknown)))
  | Unary (Not, a) -> ignore (infer env a); TPrim "Bool"
  | Unary (Neg, a) -> infer env a
  | Binary (op, a, b) -> infer_binary env op a b
  | Elvis (a, b) ->
    let _ = infer env a in
    infer env b
  | NotNull a -> (match infer env a with TNull t -> t | t -> t)
  | Field (a, f) | SafeField (a, f) ->
    let ta = infer env a in
    let base = (match e with SafeField _ -> true | _ -> false) in
    (match ta with
     | TNamed (n, _) ->
       (match Hashtbl.find_opt env.structs n with
        | Some si ->
          (match List.assoc_opt f si.fields with
           | Some ft -> if base then TNull ft else ft
           | None -> err env (Printf.sprintf "type %s has no field %s" n f); TUnknown)
        | None -> TUnknown)
     | _ -> TUnknown)
  | Static (Ident base, _) when Hashtbl.mem env.enums base -> TNamed (base, [])
  | Static (a, _) -> ignore (infer env a); TUnknown
  | TypeApp (a, _) -> infer env a
  | Call (f, args) -> infer_call env f args
  | Index (a, i) -> ignore (infer env a); ignore (infer env i); TUnknown
  | ListLit es -> TNamed ("List", [ List.fold_left (fun acc e -> join acc (infer env e)) TUnknown es ])
  | MapLit kvs ->
    List.iter (fun (k, v) -> ignore (infer env k); ignore (infer env v)) kvs;
    TNamed ("Map", [ TUnknown; TUnknown ])
  | Lambda (params, body) ->
    with_scope env (fun () ->
        let ptys = List.map (fun lp -> match lp.lp_ty with Some t -> of_ast t | None -> TUnknown) params in
        List.iter2 (fun lp t -> bind env lp.lp_name t) params ptys;
        TFun (ptys, infer env body))
  | If (c, t, eo) ->
    require_bool env (infer env c) "if";
    let tt = infer env t in
    (match eo with Some el -> join tt (infer env el) | None -> tt)
  | When (subject, arms) ->
    Option.iter (fun s -> ignore (infer env s.ws_expr)) subject;
    List.fold_left
      (fun acc arm ->
        with_scope env (fun () ->
            (match arm.wa_lhs with
             | LhsElse -> ()
             | LhsCond c -> require_bool env (infer env c) "when"
             | LhsPatterns pats -> List.iter (bind_pattern env) pats);
            Option.iter (fun s -> Option.iter (fun n -> bind env n TUnknown) s.ws_bind) subject;
            Option.iter (fun g -> require_bool env (infer env g) "guard") arm.wa_guard;
            join acc (infer env arm.wa_body)))
      TUnknown arms
  | Block (stmts, result) ->
    with_scope env (fun () ->
        List.iter (check_stmt env) stmts;
        match result with Some e -> infer env e | None -> TPrim "Unit")

and infer_binary env op a b =
  let ta = infer env a and tb = infer env b in
  match op with
  | Add | Sub | Mul | Div | Mod ->
    if op = Add && (ta = TPrim "String" || tb = TPrim "String") then TPrim "String"
    else if is_numeric ta && is_numeric tb then join ta tb
    else if ta = TUnknown || tb = TUnknown then TUnknown
    else (
      err env (Printf.sprintf "arithmetic on non-numeric operands: %s and %s" (show ta) (show tb));
      TUnknown)
  | Eq | Neq -> TPrim "Bool"
  | Lt | Gt | Le | Ge -> TPrim "Bool"
  | And | Or ->
    require_bool env ta "logical operator";
    require_bool env tb "logical operator";
    TPrim "Bool"
  | BAnd | BOr | BXor | Shl | Shr ->
    if is_numeric ta && is_numeric tb then join ta tb
    else if ta = TUnknown || tb = TUnknown then TUnknown
    else (
      err env (Printf.sprintf "bitwise operator on non-numeric operands: %s and %s" (show ta) (show tb));
      TUnknown)
  | Range -> TNamed ("Range", [ join ta tb ])

and infer_call env f args =
  let tf = infer env f in
  List.iter (fun a -> ignore (infer env a.arg_val)) args;
  match tf with
  | TFun (params, ret) ->
    if List.length params <> List.length args then (
      err env
        (Printf.sprintf "wrong number of arguments: expected %d, got %d" (List.length params)
           (List.length args));
      ret)
    else
      (* A bare type parameter (single-uppercase head) is instantiated by unification: bind it to the arg
         type and check cross-occurrence consistency. Everything else keeps the exact prior structural
         compat check, so non-generic calls are byte-identical to before. The generic return type is then
         instantiated with the collected substitution. *)
      let gens = match f with
        | Ident name -> (match Hashtbl.find_opt env.fun_gens name with Some g -> g | None -> [])
        | _ -> [] in
      let subst = ref [] in
      List.iter2
        (fun pt a ->
          let at = infer env a.arg_val in
          if is_type_param_ty pt then (
            bind_type_var env subst (head_name pt) at;
            check_bound env gens (head_name pt) at)
          else if not (compat at pt) then
            err env (Printf.sprintf "argument type %s is not compatible with parameter %s" (show at) (show pt)))
        params args;
      inst_ty subst ret
  | _ -> TUnknown

and require_bool env t ctx =
  if not (compat t (TPrim "Bool")) then
    err env (Printf.sprintf "%s condition must be Bool, found %s" ctx (show t))

and bind_pattern env pat =
  match pat with
  | PWild | PLitInt _ | PLitFloat _ | PLitString _ | PLitChar _ | PLitBool _ | PLitNull
  | PPath _ | PIs _ -> ()
  | PBind s -> bind env s TUnknown
  | PIn (e, _) -> ignore (infer env e)
  | PCtor (_, CPPos pats) -> List.iter (bind_pattern env) pats
  | PCtor (_, CPRecord (fields, _)) ->
    List.iter (fun f -> match f.rf_pat with Some p -> bind_pattern env p | None -> bind env f.rf_name TUnknown) fields

and check_stmt env s =
  match s with
  | SLet { name; ty; init; _ } ->
    let it = infer env init in
    (match ty with
     | Some declared ->
       let dt = of_ast declared in
       if not (compat it dt) then
         err env (Printf.sprintf "cannot assign %s to %s %s" (show it) (show dt) name);
       bind env name dt
     | None -> bind env name it)
  | SExpr e -> ignore (infer env e)
  | SAssign (l, r) -> ignore (infer env l); ignore (infer env r)
  | SReturn eo ->
    let t = match eo with Some e -> infer env e | None -> TPrim "Unit" in
    (match env.cur_ret with
     | Some rt when not (compat t rt) ->
       err env (Printf.sprintf "return type %s is not compatible with %s" (show t) (show rt))
     | _ -> ())
  | SWhile (c, b) -> require_bool env (infer env c) "while"; ignore (infer env b)
  | SFor { var; iter; body } ->
    ignore (infer env iter);
    with_scope env (fun () -> bind env var TUnknown; ignore (infer env body))
  | SBreak | SContinue -> ()

let check_fun env fd =
  match fd.fn_body with
  | None -> ()
  | Some body ->
    with_scope env (fun () ->
        List.iter (fun p -> bind env p.pname (of_ast p.pty)) fd.fn_params;
        let ret = match fd.fn_ret with Some t -> of_ast t | None -> TPrim "Unit" in
        env.cur_ret <- Some ret;
        let bt = infer env body in
        (* an `= expr` body, or a block ending in a trailing value, must match the
           declared return; a block ending in statements returns via `return`
           (checked per-statement) and falls through to Unit — don't re-check it *)
        let should_check = match body with Block (_, None) -> false | _ -> true in
        if should_check && fd.fn_ret <> None && not (compat bt ret) && bt <> TPrim "Nothing" then
          err env
            (Printf.sprintf "function %s body has type %s, expected %s" fd.fn_name (show bt) (show ret));
        env.cur_ret <- None)

let check_decl env d =
  match d with
  | FunDecl fd -> check_fun env fd
  | StructDecl td | ClassDecl td ->
    Option.iter (fun e -> with_scope env (fun () -> ignore (infer env e))) td.td_deinit;
    List.iter (check_fun env) td.td_methods
  | TraitDecl tr -> List.iter (check_fun env) tr.tr_methods
  | ImplDecl im -> List.iter (check_fun env) im.im_methods
  | EnumDecl _ | Import _ -> ()

let check (prog : program) : string list =
  let env =
    {
      funs = Hashtbl.create 64;
      fun_gens = Hashtbl.create 64;
      structs = Hashtbl.create 64;
      enums = Hashtbl.create 32;
      impls = ref [];
      locals = [];
      cur_ret = None;
      diags = ref [];
    }
  in
  (* pass A: collect signatures *)
  List.iter
    (fun d ->
      match d with
      | FunDecl fd ->
        Hashtbl.replace env.funs fd.fn_name
          (List.map (fun p -> of_ast p.pty) fd.fn_params,
           (match fd.fn_ret with Some t -> of_ast t | None -> TPrim "Unit"));
        Hashtbl.replace env.fun_gens fd.fn_name fd.fn_generics
      | StructDecl td | ClassDecl td ->
        Hashtbl.replace env.structs td.td_name
          { fields = List.map (fun f -> (f.cf_name, of_ast f.cf_ty)) td.td_fields }
      | EnumDecl ed -> Hashtbl.replace env.enums ed.ed_name ()
      | ImplDecl im ->
        (match im.im_trait with
         | Some (path, _) ->
           let tr = List.nth path (List.length path - 1) in
           env.impls := (head_name (of_ast im.im_type), tr) :: !(env.impls)
         | None -> ())
      | TraitDecl _ | Import _ -> ())
    prog;
  (* pass B: check bodies *)
  List.iter (check_decl env) prog;
  List.rev !(env.diags)
