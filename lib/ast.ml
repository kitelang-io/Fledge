(* Abstract syntax tree for the Kite bootstrap subset.
   Kite is expression-oriented: `if`, `when`, and `{ ... }` blocks are all
   expressions that produce a value. *)

type ty =
  | TyPath of string list * ty list  (* path segments + type args: Int, List<T>, kite::io::File *)
  | TyNullable of ty                 (* T? *)
  | TyFun of ty list * ty            (* (A, B) -> R function type *)

type unop =
  | Neg                    (* -e *)
  | Not                    (* !e *)

type binop =
  | Add | Sub | Mul | Div | Mod
  | Eq | Neq | Lt | Gt | Le | Ge
  | And | Or
  | BAnd | BOr | BXor | Shl | Shr   (* bitwise & | ^, shifts << >> *)
  | Range                  (* a..b *)

type expr =
  | IntLit of int
  | FloatLit of float
  | StringLit of string
  | CharLit of int
  | BoolLit of bool
  | NullLit
  | This
  | Ident of string
  | Unary of unop * expr
  | Binary of binop * expr * expr
  | Elvis of expr * expr             (* a ?: b *)
  | NotNull of expr                  (* e!! *)
  | Field of expr * string           (* e.name *)
  | SafeField of expr * string       (* e?.name *)
  | Static of expr * string          (* e::name — path / associated / enum-variant *)
  | Call of expr * arg list          (* callee(args) — also struct construction *)
  | Index of expr * expr             (* e[i] *)
  | TypeApp of expr * ty list        (* turbofish: f::<T> *)
  | ListLit of expr list             (* [a, b, c] *)
  | MapLit of (expr * expr) list     (* ["k": v, ...] *)
  | Lambda of lam_param list * expr  (* { x, y -> body } ; params [] = implicit `it` *)
  | If of expr * expr * expr option  (* if (c) then [else] — an expression *)
  | When of when_subject option * when_arm list
  | Block of stmt list * expr option (* { stmts...; optional trailing value } *)
  | Interp of interp_part list       (* "text $x ${e}" interpolated string *)
  | EReturn of expr option           (* return as a diverging expression (type Nothing) *)
  | EBreak
  | EContinue

and interp_part = ILit of string | IExpr of expr

(* a call argument, optionally named: `f(x = 1, y)` *)
and arg = { arg_name : string option; arg_val : expr }

(* a lambda parameter: `x` or `x: T` *)
and lam_param = { lp_name : string; lp_ty : ty option }

(* when (val n = consuming? expr) — the matched subject *)
and when_subject = { ws_bind : string option; ws_consuming : bool; ws_expr : expr }

and when_arm = { wa_lhs : arm_lhs; wa_guard : expr option; wa_body : expr }
and arm_lhs =
  | LhsElse
  | LhsPatterns of pattern list      (* subject form: pattern (| pattern)* *)
  | LhsCond of expr                  (* subject-less form: boolean condition *)

and pattern =
  | PWild                            (* _ *)
  | PBind of string                  (* fresh lowercase binding *)
  | PLitInt of int
  | PLitFloat of float
  | PLitString of string
  | PLitChar of int
  | PLitBool of bool
  | PLitNull
  | PPath of string list             (* unit variant / const: None, Color::Red *)
  | PCtor of string list * ctor_pat_args   (* Some(v), Point(x = 0, ..) *)
  | PIs of ty * bool                 (* is T / !is T *)
  | PIn of expr * bool               (* in e / !in e *)

and ctor_pat_args =
  | CPPos of pattern list                        (* Some(v), Bin(op, l, r) *)
  | CPRecord of record_field_pat list * bool     (* fields, trailing `..` present? *)

and record_field_pat = { rf_name : string; rf_pat : pattern option }

and stmt =
  | SLet of { name : string; ty : ty option; init : expr; is_var : bool }
  | SExpr of expr
  | SAssign of expr * expr           (* lvalue = expr *)
  | SReturn of expr option
  | SWhile of expr * expr            (* cond, body-block *)
  | SFor of { var : string; iter : expr; body : expr }
  | SBreak
  | SContinue

type pmode = PMNormal | PMInout | PMConsuming
type param = { pname : string; pmode : pmode; pty : ty }
type receiver = RSelf | RMutSelf | RConsumingSelf

(* <T: Bound + Bound, U = Default> *)
type generic_param = { gp_name : string; gp_bounds : ty list; gp_default : ty option }
type generics = generic_param list

(* where T: A + B, U: C — each entry is (constrained type, bounds) *)
type where_clause = (ty * ty list) list

(* @name(args) — e.g. @derive(Eq, Ord), @inline, @repr(transparent) *)
type annotation = { an_name : string; an_args : expr list }

type fundecl = {
  fn_annos : annotation list;
  fn_name : string;
  fn_generics : generics;
  fn_receiver : receiver option;      (* Some when it is a method *)
  fn_params : param list;
  fn_ret : ty option;
  fn_where : where_clause;
  fn_body : expr option;              (* None = signature only (trait method sig) *)
}

(* a field declared in a struct/class primary constructor *)
type ctor_field = { cf_pub : bool; cf_mut : bool; cf_name : string; cf_ty : ty }

type type_decl = {
  td_annos : annotation list;
  td_name : string;
  td_generics : generics;
  td_fields : ctor_field list;
  td_where : where_clause;
  td_deinit : expr option;
  td_methods : fundecl list;          (* inherent methods in the brace body *)
}

type variant_payload =
  | PNone
  | PPositional of ty list            (* Some(T), Bin(Op, Expr, Expr) *)
  | PNamed of ctor_field list         (* Subprocess(code: Int32) *)

type variant = { var_name : string; var_payload : variant_payload }

type enum_decl = {
  ed_annos : annotation list;
  ed_name : string;
  ed_generics : generics;
  ed_variants : variant list;
}

type trait_decl = {
  tr_annos : annotation list;
  tr_name : string;
  tr_generics : generics;
  tr_supers : ty list;                (* supertraits: trait A: B + C *)
  tr_where : where_clause;
  tr_assoc : (string * ty list) list; (* associated types: type Item [: bounds] *)
  tr_methods : fundecl list;          (* sigs (fn_body = None) and default methods *)
}

type impl_decl = {
  im_annos : annotation list;
  im_generics : generics;
  im_trait : (string list * ty list) option; (* Some(path,args) for `impl Trait for Type`; None = inherent *)
  im_type : ty;
  im_where : where_clause;
  im_assoc : (string * ty) list;      (* associated-type bindings: type Output = Vec2 *)
  im_methods : fundecl list;
}

type decl =
  | FunDecl of fundecl
  | StructDecl of type_decl            (* value type *)
  | ClassDecl of type_decl             (* reference type, ARC *)
  | EnumDecl of enum_decl
  | TraitDecl of trait_decl
  | ImplDecl of impl_decl
  | Import of string list              (* import kite::io  ->  ["kite"; "io"] *)

type program = decl list
