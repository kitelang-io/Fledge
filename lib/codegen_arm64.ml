(* M4 (walking skeleton) — a minimal self-built AArch64 / Mach-O backend.

   Lowers a small monomorphic subset directly from the AST to arm64 assembly:
   `Int` functions, `val`/`var` locals, `return`, arithmetic (+ - * / %),
   comparisons, logic, unary neg, `if`/`else`, `while`, `for i in a..b`, `when`
   over integers, calls & recursion, and `println`/`print` (via libc printf).
   A stack-machine evaluation strategy keeps it simple and correct (temporaries
   on the CPU stack). `main`'s Int result becomes the process exit code.

   Everything outside the subset raises Codegen_error — the backend widens over
   later increments (IR + ARC, register allocation, more types).

   Codegen builds a typed instruction IR (`instr list`). Two backends consume it:
   `print_instr` renders assembly text (for `kitec asm` inspection), and `assemble`
   /`encode_instr` produce raw AArch64 machine-code words + relocations. Fledge now
   SELF-LINKS: it writes both its own Mach-O object (`kitec obj`) and a fully-linked,
   directly-runnable Mach-O executable (`kitec run`/`exe`) via `lib/macho.ml`.
   `kitec run` goes parse -> codegen -> encode -> write MH_EXECUTE (Fledge) ->
   execute. NO external assembler or linker (as/ld/clang) is invoked anywhere;
   only dyld loads the produced binary at runtime. *)

open Ast

exception Codegen_error of string

let spf = Printf.sprintf
let align16 n = (n + 15) land lnot 15

let label_counter = ref 0
let fresh () = incr label_counter; !label_counter

(* Interned user string literals -> a __cstring label. Populated during codegen,
   emitted by program_instrs / cstring_section, resolved by the linker. *)
let string_labels : (string, string) Hashtbl.t = Hashtbl.create 16
let user_strings : (string * string) list ref = ref [] (* (label, content), creation order reversed *)
let string_ctr = ref 0

let intern_string s =
  match Hashtbl.find_opt string_labels s with
  | Some l -> l
  | None ->
    incr string_ctr;
    let l = spf "Lstr_%d" !string_ctr in
    Hashtbl.replace string_labels s l;
    user_strings := (l, s) :: !user_strings;
    l

(* built-in printf format strings *)
let cstring_format_entries =
  [ ("Lfmt_println", "%ld\n\000"); ("Lfmt_print", "%ld\000");
    ("Lfmt_println_s", "%s\n\000"); ("Lfmt_print_s", "%s\000");
    ("Lfmt_ld", "%ld\000") ]

(* every __cstring literal in layout order: formats first, then user strings *)
let all_cstrings () =
  cstring_format_entries @ List.map (fun (l, s) -> (l, s ^ "\000")) (List.rev !user_strings)

(* ------------------------------------------------------------------ *)
(* Typed instruction IR                                               *)
(* ------------------------------------------------------------------ *)

(* General-purpose register operand: 0..30 => x0..x30, and 31 => sp/xzr/wzr
   depending on position. Most instructions that touch register 31 hardcode
   the correct name (Push/Pop, StpFp/LdpFp, MovFpSp, MovZero, SpAdd/SpSub,
   StrSp/LdrSp); the load/store and add/sub-imm printers use `rb`/`rw` (below)
   so a 31 in a base or data-source slot renders as sp/wzr, matching the
   encoder and keeping the printed asm assemblable. *)
type reg = int

(* Condition mnemonic exactly as it appears in the assembly ("eq","ne",...). *)
type cond = string

type instr =
  (* immediates / moves *)
  | Movz of reg * int              (* movz Xd, #imm *)
  | Movk of reg * int * int        (* movk Xd, #imm, lsl #sh *)
  | Neg of reg * reg               (* neg Xd, Xm *)
  | MovReg of reg * reg            (* mov Xd, Xm *)
  | MovZero of reg                 (* mov Xd, xzr *)
  | MovFpSp                        (* mov x29, sp *)
  (* arithmetic / logic, reg-reg-reg *)
  | Add of reg * reg * reg
  | Sub of reg * reg * reg
  | Mul of reg * reg * reg
  | Sdiv of reg * reg * reg
  | Msub of reg * reg * reg * reg
  | And of reg * reg * reg
  | Orr of reg * reg * reg
  | Eor of reg * reg * reg         (* eor Xd, Xn, Xm  (bitwise xor) *)
  | Lslv of reg * reg * reg        (* lsl Xd, Xn, Xm  (variable left shift) *)
  | Asrv of reg * reg * reg        (* asr Xd, Xn, Xm  (variable arith. right shift) *)
  | AddImm of reg * reg * int      (* add Xd, Xn, #imm *)
  | SubImm of reg * reg * int      (* sub Xd, Xn, #imm  (imm12, unsigned) *)
  (* stack-pointer adjustment *)
  | SpAdd of int                   (* add sp, sp, #imm *)
  | SpSub of int                   (* sub sp, sp, #imm *)
  (* loads / stores *)
  | LdrFp of reg * int             (* ldr Xt, [x29, #-off] *)
  | StrFp of reg * int             (* str Xt, [x29, #-off] *)
  | LdrO of reg * reg * int        (* ldr Xt, [Xn, #off]  (off >= 0, multiple of 8) *)
  | StrO of reg * reg * int        (* str Xt, [Xn, #off] *)
  | LdrB of reg * reg * int        (* ldrb Wt, [Xn, #off]  (zero-extended byte load) *)
  | StrB of reg * reg * int        (* strb Wt, [Xn, #off]  (byte store) *)
  | LdrSp of reg                   (* ldr Xt, [sp]            (peek) *)
  | StrSp of reg                   (* str Xt, [sp] *)
  | Push of reg                    (* str Xt, [sp, #-16]!     (pre-index) *)
  | Pop of reg                     (* ldr Xt, [sp], #16       (post-index) *)
  | StpFp                          (* stp x29, x30, [sp, #-16]! *)
  | LdpFp                          (* ldp x29, x30, [sp], #16 *)
  (* compare / condition *)
  | Cmp of reg * reg               (* cmp Xn, Xm *)
  | Cset of reg * cond             (* cset Xd, cond *)
  (* control flow *)
  | B of string                    (* b label *)
  | Bcond of cond * string         (* b.<cond> label *)
  | Cbz of reg * string            (* cbz Xt, label *)
  | Bl of string                   (* bl symbol  (symbol includes leading _) *)
  | Ret
  (* address materialization *)
  | Adrp of reg * string           (* adrp Xd, sym@PAGE *)
  | AddSym of reg * reg * string   (* add Xd, Xn, sym@PAGEOFF *)
  (* structure *)
  | Label of string                (* label: *)
  | Raw of string                  (* verbatim text (directives / data / header) *)

let rn (r : reg) = "x" ^ string_of_int r
(* Register 31 is `sp` in the base position of a load/store or add/sub-imm,
   and `wzr`/`xzr` as a data source — never `x31`. The encoder already emits
   the right bit pattern; these keep the printed asm assemblable to match. *)
let rb (r : reg) = if r = 31 then "sp" else "x" ^ string_of_int r
let rw (r : reg) = if r = 31 then "wzr" else "w" ^ string_of_int r

let print_instr = function
  | Movz (d, i) -> spf "\tmovz %s, #%d\n" (rn d) i
  | Movk (d, i, sh) -> spf "\tmovk %s, #%d, lsl #%d\n" (rn d) i sh
  | Neg (d, m) -> spf "\tneg %s, %s\n" (rn d) (rn m)
  | MovReg (d, m) -> spf "\tmov %s, %s\n" (rn d) (rn m)
  | MovZero d -> spf "\tmov %s, xzr\n" (rn d)
  | MovFpSp -> "\tmov x29, sp\n"
  | Add (d, n, m) -> spf "\tadd %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Sub (d, n, m) -> spf "\tsub %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Mul (d, n, m) -> spf "\tmul %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Sdiv (d, n, m) -> spf "\tsdiv %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Msub (d, n, m, a) -> spf "\tmsub %s, %s, %s, %s\n" (rn d) (rn n) (rn m) (rn a)
  | And (d, n, m) -> spf "\tand %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Orr (d, n, m) -> spf "\torr %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Eor (d, n, m) -> spf "\teor %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Lslv (d, n, m) -> spf "\tlsl %s, %s, %s\n" (rn d) (rn n) (rn m)
  | Asrv (d, n, m) -> spf "\tasr %s, %s, %s\n" (rn d) (rn n) (rn m)
  | AddImm (d, n, i) -> spf "\tadd %s, %s, #%d\n" (rn d) (rb n) i
  | SubImm (d, n, i) -> spf "\tsub %s, %s, #%d\n" (rn d) (rb n) i
  | SpAdd i -> spf "\tadd sp, sp, #%d\n" i
  | SpSub i -> spf "\tsub sp, sp, #%d\n" i
  | LdrFp (t, off) -> spf "\tldr %s, [x29, #-%d]\n" (rn t) off
  | StrFp (t, off) -> spf "\tstr %s, [x29, #-%d]\n" (rn t) off
  | LdrO (t, n, off) -> spf "\tldr %s, [%s, #%d]\n" (rn t) (rb n) off
  | StrO (t, n, off) -> spf "\tstr %s, [%s, #%d]\n" (rn t) (rb n) off
  | LdrB (t, n, off) -> spf "\tldrb %s, [%s, #%d]\n" (rw t) (rb n) off
  | StrB (t, n, off) -> spf "\tstrb %s, [%s, #%d]\n" (rw t) (rb n) off
  | LdrSp t -> spf "\tldr %s, [sp]\n" (rn t)
  | StrSp t -> spf "\tstr %s, [sp]\n" (rn t)
  | Push t -> spf "\tstr %s, [sp, #-16]!\n" (rn t)
  | Pop t -> spf "\tldr %s, [sp], #16\n" (rn t)
  | StpFp -> "\tstp x29, x30, [sp, #-16]!\n"
  | LdpFp -> "\tldp x29, x30, [sp], #16\n"
  | Cmp (n, m) -> spf "\tcmp %s, %s\n" (rn n) (rn m)
  | Cset (d, c) -> spf "\tcset %s, %s\n" (rn d) c
  | B l -> spf "\tb %s\n" l
  | Bcond (c, l) -> spf "\tb.%s %s\n" c l
  | Cbz (t, l) -> spf "\tcbz %s, %s\n" (rn t) l
  | Bl sym -> spf "\tbl %s\n" sym
  | Ret -> "\tret\n"
  | Adrp (d, sym) -> spf "\tadrp %s, %s@PAGE\n" (rn d) sym
  | AddSym (d, n, sym) -> spf "\tadd %s, %s, %s@PAGEOFF\n" (rn d) (rn n) sym
  | Label l -> spf "%s:\n" l
  | Raw s -> s

(* ------------------------------------------------------------------ *)
(* Machine-code encoder (instr -> 32-bit AArch64 words)               *)
(* ------------------------------------------------------------------ *)

(* A pending relocation to be resolved by the Mach-O writer / linker.
   [r_off] is the byte offset of the instruction word within the text
   section; [r_sym] the target symbol (with its leading '_'). *)
type reloc_kind = RelocBranch26 | RelocPage21 | RelocPageoff12

type reloc = { r_off : int; r_sym : string; r_kind : reloc_kind }

(* Does this instruction emit exactly one 32-bit word? Label/Raw do not. *)
let is_word = function Label _ | Raw _ -> false | _ -> true

(* Condition mnemonic -> 4-bit AArch64 condition code. *)
let cond_code = function
  | "eq" -> 0 | "ne" -> 1 | "cs" | "hs" -> 2 | "cc" | "lo" -> 3
  | "mi" -> 4 | "pl" -> 5 | "vs" -> 6 | "vc" -> 7
  | "hi" -> 8 | "ls" -> 9 | "ge" -> 10 | "lt" -> 11
  | "gt" -> 12 | "le" -> 13 | "al" -> 14
  | c -> raise (Codegen_error (spf "unknown condition `%s`" c))

(* Encode one word-producing instruction.
   [labels] maps local label -> byte offset; [here] is this word's byte offset.
   Returns the 32-bit word and, for cross-symbol references, a pending reloc. *)
let encode_instr labels here instr : int * reloc option =
  let word w = (w land 0xffffffff, None) in
  let br_imm target = (target - here) / 4 in
  let find_label l =
    match Hashtbl.find_opt labels l with
    | Some off -> off
    | None -> raise (Codegen_error (spf "unresolved local label `%s`" l))
  in
  match instr with
  | Ret -> word 0xD65F03C0
  | Movz (d, i) -> word (0xD2800000 lor ((i land 0xffff) lsl 5) lor d)
  | Movk (d, i, sh) ->
    word (0xF2800000 lor ((sh / 16) lsl 21) lor ((i land 0xffff) lsl 5) lor d)
  | Neg (d, m) -> word (0xCB0003E0 lor (m lsl 16) lor d)
  | MovReg (d, m) -> word (0xAA0003E0 lor (m lsl 16) lor d)
  | MovZero d -> word (0xAA1F03E0 lor d)
  | MovFpSp -> word 0x910003FD
  | Add (d, n, m) -> word (0x8B000000 lor (m lsl 16) lor (n lsl 5) lor d)
  | Sub (d, n, m) -> word (0xCB000000 lor (m lsl 16) lor (n lsl 5) lor d)
  | Mul (d, n, m) ->
    word (0x9B000000 lor (m lsl 16) lor (31 lsl 10) lor (n lsl 5) lor d)
  | Sdiv (d, n, m) -> word (0x9AC00C00 lor (m lsl 16) lor (n lsl 5) lor d)
  | Msub (d, n, m, a) ->
    word (0x9B008000 lor (m lsl 16) lor (a lsl 10) lor (n lsl 5) lor d)
  | And (d, n, m) -> word (0x8A000000 lor (m lsl 16) lor (n lsl 5) lor d)
  | Orr (d, n, m) -> word (0xAA000000 lor (m lsl 16) lor (n lsl 5) lor d)
  | Eor (d, n, m) -> word (0xCA000000 lor (m lsl 16) lor (n lsl 5) lor d)
  | Lslv (d, n, m) -> word (0x9AC02000 lor (m lsl 16) lor (n lsl 5) lor d)
  | Asrv (d, n, m) -> word (0x9AC02800 lor (m lsl 16) lor (n lsl 5) lor d)
  | AddImm (d, n, i) -> word (0x91000000 lor ((i land 0xfff) lsl 10) lor (n lsl 5) lor d)
  | SubImm (d, n, i) -> word (0xD1000000 lor ((i land 0xfff) lsl 10) lor (n lsl 5) lor d)
  | SpAdd i -> word (0x91000000 lor ((i land 0xfff) lsl 10) lor (31 lsl 5) lor 31)
  | SpSub i -> word (0xD1000000 lor ((i land 0xfff) lsl 10) lor (31 lsl 5) lor 31)
  (* ldr/str Xt,[x29,#-off] -> LDUR/STUR (unscaled, signed 9-bit imm = -off) *)
  | LdrFp (t, off) -> word (0xF8400000 lor (((-off) land 0x1ff) lsl 12) lor (29 lsl 5) lor t)
  | StrFp (t, off) -> word (0xF8000000 lor (((-off) land 0x1ff) lsl 12) lor (29 lsl 5) lor t)
  | LdrSp t -> word (0xF9400000 lor (31 lsl 5) lor t)
  | StrSp t -> word (0xF9000000 lor (31 lsl 5) lor t)
  | LdrO (t, n, off) -> word (0xF9400000 lor (((off / 8) land 0xfff) lsl 10) lor (n lsl 5) lor t)
  | StrO (t, n, off) -> word (0xF9000000 lor (((off / 8) land 0xfff) lsl 10) lor (n lsl 5) lor t)
  | LdrB (t, n, off) -> word (0x39400000 lor ((off land 0xfff) lsl 10) lor (n lsl 5) lor t)
  | StrB (t, n, off) -> word (0x39000000 lor ((off land 0xfff) lsl 10) lor (n lsl 5) lor t)
  | Push t -> word (0xF8000C00 lor (((-16) land 0x1ff) lsl 12) lor (31 lsl 5) lor t)
  | Pop t -> word (0xF8400400 lor ((16 land 0x1ff) lsl 12) lor (31 lsl 5) lor t)
  | StpFp -> word 0xA9BF7BFD
  | LdpFp -> word 0xA8C17BFD
  | Cmp (n, m) -> word (0xEB000000 lor (m lsl 16) lor (n lsl 5) lor 31)
  | Cset (d, c) -> word (0x9A9F07E0 lor ((cond_code c lxor 1) lsl 12) lor d)
  | B l -> word (0x14000000 lor (br_imm (find_label l) land 0x3ffffff))
  | Bcond (c, l) ->
    word (0x54000000 lor ((br_imm (find_label l) land 0x7ffff) lsl 5) lor cond_code c)
  | Cbz (t, l) ->
    word (0xB4000000 lor ((br_imm (find_label l) land 0x7ffff) lsl 5) lor t)
  | Bl sym -> (0x94000000, Some { r_off = here; r_sym = sym; r_kind = RelocBranch26 })
  | Adrp (d, sym) -> (0x90000000 lor d, Some { r_off = here; r_sym = sym; r_kind = RelocPage21 })
  | AddSym (d, n, sym) ->
    (0x91000000 lor (n lsl 5) lor d, Some { r_off = here; r_sym = sym; r_kind = RelocPageoff12 })
  | Label _ | Raw _ -> raise (Codegen_error "encode_instr called on non-word instruction")

(* Two-pass assembler over an instruction list: pass 1 assigns every Label a
   byte offset (4 bytes per real instruction); pass 2 encodes each word,
   resolving local branches and recording cross-symbol relocations. Returns the
   text words (in order) and the pending relocations. *)
let assemble (instrs : instr list) : int array * reloc list =
  (* pass 1: label -> byte offset *)
  let labels = Hashtbl.create 64 in
  let off = ref 0 in
  List.iter
    (fun i ->
      match i with
      | Label l -> Hashtbl.replace labels l !off
      | _ -> if is_word i then off := !off + 4)
    instrs;
  (* pass 2: encode *)
  let words = ref [] and relocs = ref [] and here = ref 0 in
  List.iter
    (fun i ->
      if is_word i then begin
        let w, r = encode_instr labels !here i in
        words := w :: !words;
        (match r with Some r -> relocs := r :: !relocs | None -> ());
        here := !here + 4
      end)
    instrs;
  (Array.of_list (List.rev !words), List.rev !relocs)

(* Defined function symbols with their byte offset in the __text section, in
   program (layout) order. A function entry is any Label whose name starts with
   '_' (local labels all start with 'L'). Uses the same pass-1 offset rule as
   [assemble] (4 bytes per real instruction). *)
let function_symbols (instrs : instr list) : (string * int) list =
  let off = ref 0 and acc = ref [] in
  List.iter
    (fun i ->
      match i with
      | Label l when String.length l > 0 && l.[0] = '_' -> acc := (l, !off) :: !acc
      | _ -> if is_word i then off := !off + 4)
    instrs;
  List.rev !acc

(* ------------------------------------------------------------------ *)
(* Lowering                                                           *)
(* ------------------------------------------------------------------ *)

(* per-function lowering context; `code` accumulates the program IR (reversed) *)
(* Boxed aggregate model (bootstrap): every struct/class value is a heap pointer
   (one word). These tables give each type its size and field byte-offsets, and
   each function its return type — enough to resolve field accesses in codegen.
   (Stage-0 is throwaway: correctness over cleanliness; a typed IR + ARC come in
   the Kite self-hosted compiler.) *)
let g_struct_size : (string, int) Hashtbl.t = Hashtbl.create 16
let g_struct_fields : (string, (string * int * string) list) Hashtbl.t = Hashtbl.create 16
let g_fun_ret : (string, string) Hashtbl.t = Hashtbl.create 16
(* enum variant -> (enum name, tag index, payload type names). Boxed layout is
   {tag @ 0, payload0 @ 8, payload1 @ 16, ...}. *)
let g_variant : (string, string * int * string list) Hashtbl.t = Hashtbl.create 32

let tyname = function
  | TyPath (path, _) -> List.nth path (List.length path - 1)
  | TyNullable _ | TyFun _ -> ""

let build_types (prog : program) =
  Hashtbl.reset g_struct_size;
  Hashtbl.reset g_struct_fields;
  Hashtbl.reset g_fun_ret;
  Hashtbl.reset g_variant;
  List.iter
    (function
      | StructDecl td | ClassDecl td ->
        Hashtbl.replace g_struct_fields td.td_name
          (List.mapi (fun i f -> (f.cf_name, i * 8, tyname f.cf_ty)) td.td_fields);
        Hashtbl.replace g_struct_size td.td_name (8 * List.length td.td_fields)
      | EnumDecl ed ->
        List.iteri
          (fun tag v ->
            let ptypes =
              match v.var_payload with
              | PNone -> []
              | PPositional tys -> List.map tyname tys
              | PNamed fs -> List.map (fun f -> tyname f.cf_ty) fs
            in
            Hashtbl.replace g_variant v.var_name (ed.ed_name, tag, ptypes))
          ed.ed_variants
      | FunDecl fd ->
        (match fd.fn_ret with Some t -> Hashtbl.replace g_fun_ret fd.fn_name (tyname t) | None -> ())
      | _ -> ())
    prog

type ctx = {
  code : instr list ref;
  slots : (string, int) Hashtbl.t; (* local/param name -> byte offset below fp *)
  epi : string;                    (* epilogue label to branch to on `return` *)
  locals_ty : (string, string) Hashtbl.t; (* local/param name -> its (struct) type name *)
}

let emit ctx i = ctx.code := i :: !(ctx.code)

let rec load_imm ctx reg n =
  if n < 0 then (load_imm ctx reg (-n); emit ctx (Neg (reg, reg)))
  else begin
    emit ctx (Movz (reg, n land 0xffff));
    let chunk sh =
      let c = (n asr sh) land 0xffff in
      if c <> 0 then emit ctx (Movk (reg, c, sh))
    in
    chunk 16; chunk 32; chunk 48
  end

let push ctx = emit ctx (Push 0)

let slot ctx name =
  match Hashtbl.find_opt ctx.slots name with
  | Some off -> off
  | None -> raise (Codegen_error (spf "unknown local `%s` (codegen subset)" name))

(* Fp-relative local access. A direct LDUR/STUR carries a signed 9-bit
   immediate, so [x29, #-off] only reaches off in 8..256 (32 word slots).
   Past that we materialize the address in the scratch x16 (sub x16, x29,
   #off; ldr/str via a zero offset), which SubImm's 12-bit immediate extends
   to off <= 4095 (511 slots) — enough for any bootstrap function. x16 (IP0)
   is a caller-saved scratch never live across these two instructions. *)
let ld_fp ctx t off =
  if off <= 256 then emit ctx (LdrFp (t, off))
  else if off <= 0xfff then (emit ctx (SubImm (16, 29, off)); emit ctx (LdrO (t, 16, 0)))
  else raise (Codegen_error (spf "frame offset %d too large (too many locals in one function)" off))

let st_fp ctx t off =
  if off <= 256 then emit ctx (StrFp (t, off))
  else if off <= 0xfff then (emit ctx (SubImm (16, 29, off)); emit ctx (StrO (t, 16, 0)))
  else raise (Codegen_error (spf "frame offset %d too large (too many locals in one function)" off))

let rec gen_expr ctx e =
  match e with
  | IntLit n -> load_imm ctx 0 n
  | BoolLit b -> load_imm ctx 0 (if b then 1 else 0)
  | Ident n when Hashtbl.mem g_variant n && not (Hashtbl.mem ctx.slots n) ->
    gen_variant_new ctx n []                     (* unit enum variant, e.g. None *)
  | Ident name -> ld_fp ctx 0 (slot ctx name)
  | Unary (Neg, a) -> gen_expr ctx a; emit ctx (Neg (0, 0))
  | Binary (op, a, b) -> gen_binary ctx op a b
  | Call (Ident "println", [ a ]) ->
    (match a.arg_val with
     | StringLit s -> gen_print_str ctx (intern_string s) "Lfmt_println_s"
     | e when type_name_of_expr ctx e = Some "String" ->
       gen_print_str_val ctx e "Lfmt_println_s"
     | _ -> gen_print ctx a.arg_val "Lfmt_println")
  | Call (Ident "print", [ a ]) ->
    (match a.arg_val with
     | StringLit s -> gen_print_str ctx (intern_string s) "Lfmt_print_s"
     | e when type_name_of_expr ctx e = Some "String" ->
       gen_print_str_val ctx e "Lfmt_print_s"
     | _ -> gen_print ctx a.arg_val "Lfmt_print")
  | Call (Ident "strLen", [ a ]) ->
    gen_expr ctx a.arg_val; emit ctx (Bl "_strlen")
  | Call (Ident "charAt", [ a; i ]) ->
    gen_expr ctx a.arg_val; push ctx;      (* s on stack *)
    gen_expr ctx i.arg_val;                (* i -> x0 *)
    emit ctx (Pop 1);                      (* s -> x1 *)
    emit ctx (Add (0, 1, 0));              (* addr = s + i *)
    emit ctx (LdrB (0, 0, 0))              (* zero-extended byte -> x0 *)
  | Call (Ident "strEq", [ a; b ]) ->
    gen_expr ctx a.arg_val; push ctx;      (* a on stack *)
    gen_expr ctx b.arg_val;                (* b -> x0 *)
    emit ctx (MovReg (1, 0));              (* b -> x1 *)
    emit ctx (Pop 0);                      (* a -> x0 *)
    emit ctx (Bl "_strcmp");               (* 0 if equal -> x0 *)
    load_imm ctx 1 0; emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "eq"))
  | Call (Ident "concat", [ a; b ]) -> gen_concat ctx a.arg_val b.arg_val
  | Call (Ident "substr", [ s; start; len ]) ->
    gen_substr ctx s.arg_val start.arg_val len.arg_val
  | Call (Ident "intToStr", [ n ]) -> gen_int_to_str ctx n.arg_val
  | Call (Ident "readFile", [ p ]) -> gen_read_file ctx p.arg_val
  | Call (Ident "writeFile", [ p; c ]) -> gen_write_file ctx p.arg_val c.arg_val
  | Call (Ident "fopenW", [ p ]) -> gen_fopen_w ctx p.arg_val
  | Call (Ident "fputByte", [ b; fp ]) -> gen_fputc ctx b.arg_val fp.arg_val
  | Call (Ident "fcloseF", [ fp ]) -> gen_fclose ctx fp.arg_val
  | Call (Ident "listNew", []) -> gen_list_new ctx
  | Call (Ident "listPush", [ l; x ]) -> gen_list_push ctx l.arg_val x.arg_val
  | Call (Ident "listGet", [ l; i ]) -> gen_list_get ctx l.arg_val i.arg_val
  | Call (Ident "listSet", [ l; i; x ]) -> gen_list_set ctx l.arg_val i.arg_val x.arg_val
  | Call (Ident "listLen", [ l ]) -> gen_list_len ctx l.arg_val
  | StringLit s ->
    let l = intern_string s in
    emit ctx (Adrp (0, l));
    emit ctx (AddSym (0, 0, l))
  | Call (Ident v, args) when Hashtbl.mem g_variant v -> gen_variant_new ctx v args
  | Call (Ident n, args) when Hashtbl.mem g_struct_size n -> gen_struct_new ctx n args
  | Field (b, f) -> gen_field ctx b f
  | SafeField (b, f) -> gen_field ctx b f
  | Call (Ident f, args) -> gen_call ctx f args
  | Block (stmts, result) ->
    List.iter (gen_stmt ctx) stmts;
    (match result with Some e -> gen_expr ctx e | None -> ())
  | EReturn eo ->
    (match eo with Some e -> gen_expr ctx e | None -> ());
    emit ctx (B ctx.epi)
  | If (c, t, eo) ->
    let l = fresh () in
    let lelse = spf "Lelse_%d" l and lend = spf "Lend_%d" l in
    gen_expr ctx c;
    emit ctx (Cbz (0, lelse)); (* cond false (0) -> else *)
    gen_expr ctx t;
    emit ctx (B lend);
    emit ctx (Label lelse);
    (match eo with Some e -> gen_expr ctx e | None -> emit ctx (MovZero 0));
    emit ctx (Label lend)
  | When (subject, arms) -> gen_when ctx subject arms
  | _ -> raise (Codegen_error "expression not in the codegen subset")

and gen_binary ctx op a b =
  gen_expr ctx a;
  push ctx;                          (* a on the stack *)
  gen_expr ctx b;                    (* b in x0 *)
  emit ctx (MovReg (1, 0));          (* b -> x1 *)
  emit ctx (Pop 0);                  (* pop a -> x0 ; now x0=a, x1=b *)
  match op with
  | Add -> emit ctx (Add (0, 0, 1))
  | Sub -> emit ctx (Sub (0, 0, 1))
  | Mul -> emit ctx (Mul (0, 0, 1))
  | Div -> emit ctx (Sdiv (0, 0, 1))
  | Mod -> emit ctx (Sdiv (2, 0, 1)); emit ctx (Msub (0, 2, 1, 0))
  | Eq -> emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "eq"))
  | Neq -> emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "ne"))
  | Lt -> emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "lt"))
  | Gt -> emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "gt"))
  | Le -> emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "le"))
  | Ge -> emit ctx (Cmp (0, 1)); emit ctx (Cset (0, "ge"))
  | And -> emit ctx (And (0, 0, 1))
  | Or -> emit ctx (Orr (0, 0, 1))
  | BAnd -> emit ctx (And (0, 0, 1))
  | BOr -> emit ctx (Orr (0, 0, 1))
  | BXor -> emit ctx (Eor (0, 0, 1))
  | Shl -> emit ctx (Lslv (0, 0, 1))
  | Shr -> emit ctx (Asrv (0, 0, 1))
  | Range -> raise (Codegen_error "range not in the codegen subset")

and gen_stmt ctx s =
  match s with
  | SLet { name; ty; init; _ } ->
    gen_expr ctx init;
    st_fp ctx 0 (slot ctx name);
    let tn =
      match ty with
      | Some t -> tyname t
      | None -> (match type_name_of_expr ctx init with Some s -> s | None -> "")
    in
    if tn <> "" then Hashtbl.replace ctx.locals_ty name tn
  | SReturn eo ->
    (match eo with Some e -> gen_expr ctx e | None -> ());
    emit ctx (B ctx.epi)
  | SExpr e -> gen_expr ctx e
  | SAssign (Ident name, rhs) ->
    gen_expr ctx rhs;
    st_fp ctx 0 (slot ctx name)
  | SAssign ((Field (b, f) | SafeField (b, f)), rhs) ->
    gen_expr ctx rhs;                (* value -> x0 *)
    push ctx;                        (* save value *)
    gen_expr ctx b;                  (* base ptr -> x0 *)
    emit ctx (MovReg (1, 0));        (* ptr -> x1 *)
    emit ctx (Pop 0);                (* value -> x0 *)
    let off =
      match type_name_of_expr ctx b with
      | Some st ->
        (match Hashtbl.find_opt g_struct_fields st with
         | Some fields ->
           (match List.find_opt (fun (n, _, _) -> n = f) fields with
            | Some (_, o, _) -> o
            | None -> raise (Codegen_error (spf "field .%s not in %s (codegen)" f st)))
         | None -> raise (Codegen_error (spf "unknown aggregate type %s (codegen)" st)))
      | None -> raise (Codegen_error (spf "cannot resolve receiver type of `.%s =` (codegen)" f))
    in
    emit ctx (StrO (0, 1, off))      (* [x1 + off] = x0 *)
  | SWhile (c, body) ->
    let l = fresh () in
    let ltop = spf "Lwhile_%d" l and lend = spf "Lwend_%d" l in
    emit ctx (Label ltop);
    gen_expr ctx c;
    emit ctx (Cbz (0, lend)); (* cond false -> exit *)
    gen_expr ctx body;                    (* body block; value discarded *)
    emit ctx (B ltop);
    emit ctx (Label lend)
  | SFor { var; iter = Binary (Range, a, b); body } ->
    (* var = a; bound = b (once, kept on the stack);
       loop: if var > bound goto end; body; var = var + 1; goto loop; end *)
    gen_expr ctx a;
    st_fp ctx 0 (slot ctx var);
    gen_expr ctx b;
    push ctx;                              (* bound at [sp] *)
    let l = fresh () in
    let ltop = spf "Lfor_%d" l and lend = spf "Lfend_%d" l in
    emit ctx (Label ltop);
    ld_fp ctx 0 (slot ctx var);
    emit ctx (LdrSp 1);                    (* bound *)
    emit ctx (Cmp (0, 1));
    emit ctx (Bcond ("gt", lend));         (* var > bound -> exit *)
    gen_expr ctx body;                     (* body block; value discarded *)
    ld_fp ctx 0 (slot ctx var);
    emit ctx (AddImm (0, 0, 1));
    st_fp ctx 0 (slot ctx var);
    emit ctx (B ltop);
    emit ctx (Label lend);
    emit ctx (SpAdd 16)                    (* pop bound *)
  | SFor _ -> raise (Codegen_error "only for (i in a..b) is supported")
  | _ -> raise (Codegen_error "statement not in the codegen subset")

and gen_call ctx f args =
  (* evaluate args left-to-right, push each; then pop into x0..x{n-1} *)
  List.iter (fun a -> gen_expr ctx a.arg_val; push ctx) args;
  let n = List.length args in
  for i = n - 1 downto 0 do
    emit ctx (Pop i)
  done;
  emit ctx (Bl ("_" ^ f))

(* println(Int)/print(Int) via libc printf. Darwin passes variadic args on the
   stack: the format ptr is a named arg (x0), the Int vararg goes at [sp, #0]. *)
and gen_print ctx a fmt =
  gen_expr ctx a;                    (* Int arg -> x0 *)
  emit ctx (SpSub 16);
  emit ctx (StrSp 0);                (* vararg on the stack *)
  emit ctx (Adrp (0, fmt));
  emit ctx (AddSym (0, 0, fmt));
  emit ctx (Bl "_printf");
  emit ctx (SpAdd 16);
  emit ctx (MovZero 0)               (* print expression evaluates to 0 *)

(* println(String)/print(String): printf("%s\n"/"%s", ptr) with the string
   pointer as the (stack-passed, Darwin) variadic arg. *)
and gen_print_str ctx strlabel fmt =
  emit ctx (SpSub 16);
  emit ctx (Adrp (0, strlabel));     (* string ptr -> x0 *)
  emit ctx (AddSym (0, 0, strlabel));
  emit ctx (StrSp 0);                (* string ptr as the printf vararg at [sp] *)
  emit ctx (Adrp (0, fmt));
  emit ctx (AddSym (0, 0, fmt));
  emit ctx (Bl "_printf");
  emit ctx (SpAdd 16);
  emit ctx (MovZero 0)

(* println/print of a String *value* (a pointer computed by [e], e.g. a local or
   a concat/substr/intToStr result): printf("%s\n"/"%s", ptr). *)
and gen_print_str_val ctx e fmt =
  gen_expr ctx e;                    (* string ptr -> x0 *)
  emit ctx (SpSub 16);
  emit ctx (StrSp 0);                (* ptr as the printf vararg at [sp] *)
  emit ctx (Adrp (0, fmt));
  emit ctx (AddSym (0, 0, fmt));
  emit ctx (Bl "_printf");
  emit ctx (SpAdd 16);
  emit ctx (MovZero 0)

(* concat(a,b): la=strlen(a), lb=strlen(b), p=malloc(la+lb+1),
   memcpy(p,a,la), memcpy(p+la,b,lb+1). Values are kept on the stack across
   the libc calls; sp-relative loads use base reg 31. Leaks (no free). *)
and gen_concat ctx a b =
  gen_expr ctx a; push ctx;                (* [sp+0]=a after later pushes shift *)
  gen_expr ctx b; push ctx;
  (* stack now: [sp,0]=b [sp,16]=a *)
  emit ctx (LdrO (0, 31, 16));             (* a *)
  emit ctx (Bl "_strlen"); push ctx;       (* la *)
  emit ctx (LdrO (0, 31, 16));             (* b *)
  emit ctx (Bl "_strlen"); push ctx;       (* lb *)
  (* stack: [sp,0]=lb [sp,16]=la [sp,32]=b [sp,48]=a *)
  emit ctx (LdrO (1, 31, 16));             (* la *)
  emit ctx (Add (0, 0, 1));                (* lb+la *)
  emit ctx (AddImm (0, 0, 1));             (* +1 for NUL *)
  emit ctx (Bl "_malloc"); push ctx;       (* p *)
  (* stack: [sp,0]=p [sp,16]=lb [sp,32]=la [sp,48]=b [sp,64]=a *)
  emit ctx (LdrO (0, 31, 0));              (* dst = p *)
  emit ctx (LdrO (1, 31, 64));             (* src = a *)
  emit ctx (LdrO (2, 31, 32));             (* n = la *)
  emit ctx (Bl "_memcpy");
  emit ctx (LdrO (0, 31, 0));              (* p *)
  emit ctx (LdrO (1, 31, 32));             (* la *)
  emit ctx (Add (0, 0, 1));                (* dst = p+la *)
  emit ctx (LdrO (1, 31, 48));             (* src = b *)
  emit ctx (LdrO (2, 31, 16));             (* lb *)
  emit ctx (AddImm (2, 2, 1));             (* n = lb+1 (copy b's NUL) *)
  emit ctx (Bl "_memcpy");
  emit ctx (LdrO (0, 31, 0));              (* result = p *)
  emit ctx (SpAdd 80)                      (* pop 5 slots *)

(* substr(s,start,len): p=malloc(len+1); memcpy(p, s+start, len); p[len]=0. *)
and gen_substr ctx s start len =
  gen_expr ctx s; push ctx;
  gen_expr ctx start; push ctx;
  gen_expr ctx len; push ctx;
  (* stack: [sp,0]=len [sp,16]=start [sp,32]=s *)
  emit ctx (LdrO (0, 31, 0));              (* len *)
  emit ctx (AddImm (0, 0, 1));             (* +1 for NUL *)
  emit ctx (Bl "_malloc"); push ctx;       (* p *)
  (* stack: [sp,0]=p [sp,16]=len [sp,32]=start [sp,48]=s *)
  emit ctx (LdrO (0, 31, 0));              (* dst = p *)
  emit ctx (LdrO (1, 31, 48));             (* s *)
  emit ctx (LdrO (2, 31, 32));             (* start *)
  emit ctx (Add (1, 1, 2));                (* src = s+start *)
  emit ctx (LdrO (2, 31, 16));             (* n = len *)
  emit ctx (Bl "_memcpy");
  emit ctx (LdrO (0, 31, 0));              (* p *)
  emit ctx (LdrO (1, 31, 16));             (* len *)
  emit ctx (Add (0, 0, 1));                (* p+len *)
  emit ctx (StrB (31, 0, 0));              (* strb wzr, [p+len]  (NUL terminate) *)
  emit ctx (LdrO (0, 31, 0));              (* result = p *)
  emit ctx (SpAdd 64)                      (* pop 4 slots *)

(* intToStr(n): p=malloc(24); snprintf(p, 24, "%ld", n); return p. snprintf is
   variadic: str/size/format are fixed (x0/x1/x2), n is the Darwin stack vararg. *)
and gen_int_to_str ctx n =
  gen_expr ctx n; push ctx;                (* n on stack *)
  load_imm ctx 0 24; emit ctx (Bl "_malloc"); push ctx;  (* p *)
  (* stack: [sp,0]=p [sp,16]=n *)
  emit ctx (SpSub 16);                     (* room for the vararg *)
  (* stack: [sp,0]=vararg [sp,16]=p [sp,32]=n *)
  emit ctx (LdrO (0, 31, 32));             (* n *)
  emit ctx (StrSp 0);                      (* vararg at [sp] *)
  emit ctx (LdrO (0, 31, 16));             (* str = p *)
  load_imm ctx 1 24;                       (* size *)
  emit ctx (Adrp (2, "Lfmt_ld"));          (* format *)
  emit ctx (AddSym (2, 2, "Lfmt_ld"));
  emit ctx (Bl "_snprintf");
  emit ctx (SpAdd 16);                     (* drop vararg *)
  emit ctx (LdrO (0, 31, 0));              (* result = p *)
  emit ctx (SpAdd 32)                      (* pop 2 slots *)

(* readFile(path): fp=fopen(path,"r"); fseek(fp,0,SEEK_END); n=ftell(fp);
   fseek(fp,0,SEEK_SET); buf=malloc(n+1); fread(buf,1,n,fp); buf[n]=0;
   fclose(fp); return buf. Happy path only (assumes file exists). Leaks. *)
and gen_read_file ctx path =
  gen_expr ctx path;                       (* x0 = path *)
  let l = intern_string "r" in
  emit ctx (Adrp (1, l)); emit ctx (AddSym (1, 1, l));  (* x1 = "r" *)
  emit ctx (Bl "_fopen");                  (* x0 = fp *)
  push ctx;                                (* [sp,0]=fp *)
  emit ctx (LdrO (0, 31, 0));              (* fp *)
  load_imm ctx 1 0; load_imm ctx 2 2;      (* offset 0, SEEK_END *)
  emit ctx (Bl "_fseek");
  emit ctx (LdrO (0, 31, 0));              (* fp *)
  emit ctx (Bl "_ftell");                  (* x0 = n *)
  push ctx;                                (* [sp,0]=n [sp,16]=fp *)
  emit ctx (LdrO (0, 31, 16));             (* fp *)
  load_imm ctx 1 0; load_imm ctx 2 0;      (* offset 0, SEEK_SET *)
  emit ctx (Bl "_fseek");
  emit ctx (LdrO (0, 31, 0));              (* n *)
  emit ctx (AddImm (0, 0, 1));             (* n+1 *)
  emit ctx (Bl "_malloc");                 (* x0 = buf *)
  push ctx;                                (* [sp,0]=buf [sp,16]=n [sp,32]=fp *)
  emit ctx (LdrO (0, 31, 0));              (* buf *)
  load_imm ctx 1 1;                        (* size = 1 *)
  emit ctx (LdrO (2, 31, 16));             (* n *)
  emit ctx (LdrO (3, 31, 32));             (* fp *)
  emit ctx (Bl "_fread");
  emit ctx (LdrO (0, 31, 0));              (* buf *)
  emit ctx (LdrO (1, 31, 16));             (* n *)
  emit ctx (Add (0, 0, 1));                (* buf+n *)
  emit ctx (StrB (31, 0, 0));              (* buf[n] = 0 *)
  emit ctx (LdrO (0, 31, 32));             (* fp *)
  emit ctx (Bl "_fclose");
  emit ctx (LdrO (0, 31, 0));              (* result = buf *)
  emit ctx (SpAdd 48)                      (* pop 3 slots *)

(* writeFile(path, contents): fp=fopen(path,"w"); n=strlen(contents);
   fwrite(contents,1,n,fp); fclose(fp); return n (bytes written). Happy path. *)
and gen_write_file ctx path contents =
  gen_expr ctx path; push ctx;             (* [sp,0]=path *)
  gen_expr ctx contents; push ctx;         (* [sp,0]=contents [sp,16]=path *)
  emit ctx (LdrO (0, 31, 16));             (* path *)
  let lw = intern_string "w" in
  emit ctx (Adrp (1, lw)); emit ctx (AddSym (1, 1, lw));  (* x1 = "w" *)
  emit ctx (Bl "_fopen");                  (* x0 = fp *)
  push ctx;                                (* [sp,0]=fp [sp,16]=contents [sp,32]=path *)
  emit ctx (LdrO (0, 31, 16));             (* contents *)
  emit ctx (Bl "_strlen");                 (* x0 = n *)
  push ctx;                                (* [sp,0]=n [sp,16]=fp [sp,32]=contents [sp,48]=path *)
  emit ctx (LdrO (0, 31, 32));             (* contents *)
  load_imm ctx 1 1;                        (* size = 1 *)
  emit ctx (LdrO (2, 31, 0));              (* n *)
  emit ctx (LdrO (3, 31, 16));             (* fp *)
  emit ctx (Bl "_fwrite");
  emit ctx (LdrO (0, 31, 16));             (* fp *)
  emit ctx (Bl "_fclose");
  emit ctx (LdrO (0, 31, 0));              (* result = n *)
  emit ctx (SpAdd 64)                      (* pop 4 slots *)

(* low-level binary file I/O (for the Mach-O writer): fopenW(path)->fp,
   fputByte(byte,fp)->fputc, fcloseF(fp). Byte values 0..255; a NUL-safe way to
   emit arbitrary binary (writeFile stops at the first NUL). *)
and gen_fopen_w ctx path =
  gen_expr ctx path;                       (* x0 = path *)
  let lw = intern_string "w" in
  emit ctx (Adrp (1, lw)); emit ctx (AddSym (1, 1, lw));  (* x1 = "w" *)
  emit ctx (Bl "_fopen")                   (* x0 = fp *)
and gen_fputc ctx byte fp =
  gen_expr ctx byte; push ctx;             (* byte on stack *)
  gen_expr ctx fp; emit ctx (MovReg (1, 0)); emit ctx (Pop 0);  (* x0=byte, x1=fp *)
  emit ctx (Bl "_fputc")
and gen_fclose ctx fp =
  gen_expr ctx fp;                         (* x0 = fp *)
  emit ctx (Bl "_fclose")

(* Growable List: boxed header {len@0, cap@8, data@16} (malloc 24); data is a
   separate malloc(cap*8) of word-sized elements (Int or boxed ptr). Leaks. *)
and gen_list_new ctx =
  load_imm ctx 0 24; emit ctx (Bl "_malloc"); push ctx;  (* header on stack *)
  load_imm ctx 0 32; emit ctx (Bl "_malloc");            (* data(cap=4) -> x0 *)
  emit ctx (LdrSp 1);                       (* header -> x1 *)
  emit ctx (StrO (0, 1, 16));               (* header.data = data *)
  emit ctx (MovZero 0);                     (* len = 0 *)
  emit ctx (StrO (0, 1, 0));
  load_imm ctx 0 4;                         (* cap = 4 *)
  emit ctx (StrO (0, 1, 8));
  emit ctx (Pop 0)                          (* result = header *)

(* listPush(l, x): grow (cap*2, realloc) when full, then data[len]=x; len+=1 *)
and gen_list_push ctx l x =
  let n = fresh () in
  let store = spf "Lpush_store_%d" n in
  gen_expr ctx l; push ctx;                 (* [sp,16]=header *)
  gen_expr ctx x; push ctx;                 (* [sp,0]=x *)
  emit ctx (LdrO (1, 31, 16));              (* x1 = header *)
  emit ctx (LdrO (0, 1, 0));                (* x0 = len *)
  emit ctx (LdrO (2, 1, 8));                (* x2 = cap *)
  emit ctx (Cmp (0, 2));
  emit ctx (Bcond ("ne", store));           (* len != cap -> no grow *)
  (* grow: newcap = cap*2 *)
  emit ctx (Add (2, 2, 2));                 (* x2 = newcap *)
  emit ctx (StrO (2, 1, 8));                (* header.cap = newcap *)
  emit ctx (LdrO (0, 1, 16));               (* x0 = old data (realloc ptr) *)
  load_imm ctx 3 8; emit ctx (Mul (1, 2, 3)); (* x1 = newcap*8 (realloc size) *)
  emit ctx (Bl "_realloc");                 (* x0 = new data *)
  emit ctx (LdrO (1, 31, 16));              (* reload header -> x1 *)
  emit ctx (StrO (0, 1, 16));               (* header.data = new data *)
  emit ctx (Label store);
  emit ctx (LdrO (1, 31, 16));              (* x1 = header *)
  emit ctx (LdrO (0, 1, 0));                (* x0 = len *)
  emit ctx (LdrO (2, 1, 16));               (* x2 = data *)
  load_imm ctx 3 8; emit ctx (Mul (4, 0, 3)); (* x4 = len*8 *)
  emit ctx (Add (2, 2, 4));                 (* x2 = &data[len] *)
  emit ctx (LdrO (3, 31, 0));               (* x3 = x *)
  emit ctx (StrO (3, 2, 0));                (* data[len] = x *)
  emit ctx (AddImm (0, 0, 1));              (* len += 1 *)
  emit ctx (StrO (0, 1, 0));                (* header.len = len+1 *)
  emit ctx (SpAdd 32);                      (* pop x and header *)
  emit ctx (MovZero 0)                      (* return 0 *)

(* listGet(l, i): return data[i] *)
and gen_list_get ctx l i =
  gen_expr ctx l; push ctx;                 (* header on stack *)
  gen_expr ctx i;                           (* i -> x0 *)
  emit ctx (LdrSp 1);                       (* header -> x1 *)
  emit ctx (LdrO (1, 1, 16));               (* data -> x1 *)
  load_imm ctx 2 8; emit ctx (Mul (0, 0, 2)); (* x0 = i*8 *)
  emit ctx (Add (1, 1, 0));                 (* &data[i] *)
  emit ctx (LdrO (0, 1, 0));                (* x0 = data[i] *)
  emit ctx (SpAdd 16)                       (* pop header *)

(* listSet(l, i, x): data[i] = x ; leaves x in x0 *)
and gen_list_set ctx l i x =
  gen_expr ctx l; push ctx;                 (* [sp,0]=header *)
  gen_expr ctx i; push ctx;                 (* [sp,0]=i [sp,16]=header *)
  gen_expr ctx x;                           (* x0 = value *)
  emit ctx (LdrO (1, 31, 16));              (* header -> x1 *)
  emit ctx (LdrO (1, 1, 16));               (* data -> x1 *)
  emit ctx (LdrO (2, 31, 0));               (* i -> x2 *)
  load_imm ctx 3 8; emit ctx (Mul (2, 2, 3)); (* x2 = i*8 *)
  emit ctx (Add (1, 1, 2));                 (* &data[i] *)
  emit ctx (StrO (0, 1, 0));                (* data[i] = value *)
  emit ctx (SpAdd 32)                       (* pop i, header *)

(* listLen(l): return len *)
and gen_list_len ctx l =
  gen_expr ctx l;                           (* header -> x0 *)
  emit ctx (LdrO (0, 0, 0))                 (* x0 = len *)

(* struct/class construction: malloc the boxed object, store each field, leave
   the heap pointer in x0. Positional or named args. Bootstrap leaks (no free). *)
and gen_struct_new ctx name args =
  let size = Hashtbl.find g_struct_size name in
  let fields = Hashtbl.find g_struct_fields name in
  load_imm ctx 0 (if size <= 0 then 8 else size);
  emit ctx (Bl "_malloc");           (* heap ptr -> x0 *)
  push ctx;                          (* keep ptr on the stack across field evals *)
  List.iteri
    (fun i arg ->
      let off =
        match arg.arg_name with
        | Some fn -> let _, o, _ = List.find (fun (n, _, _) -> n = fn) fields in o
        | None -> let _, o, _ = List.nth fields i in o
      in
      gen_expr ctx arg.arg_val;      (* field value -> x0 *)
      emit ctx (LdrSp 1);            (* ptr -> x1 *)
      emit ctx (StrO (0, 1, off)))   (* [x1 + off] = x0 *)
    args;
  emit ctx (Pop 0)                   (* result = ptr in x0 *)

(* field access e.f : load the field at its byte offset from the base pointer *)
and gen_field ctx b f =
  gen_expr ctx b;                    (* base ptr -> x0 *)
  let off =
    match type_name_of_expr ctx b with
    | Some st ->
      (match Hashtbl.find_opt g_struct_fields st with
       | Some fields ->
         (match List.find_opt (fun (n, _, _) -> n = f) fields with
          | Some (_, o, _) -> o
          | None -> raise (Codegen_error (spf "field .%s not in %s (codegen)" f st)))
       | None -> raise (Codegen_error (spf "unknown aggregate type %s (codegen)" st)))
    | None -> raise (Codegen_error (spf "cannot resolve the receiver type of .%s (codegen)" f))
  in
  emit ctx (LdrO (0, 0, off))        (* x0 = [x0 + off] *)

(* best-effort static type of an expression, enough to resolve field offsets *)
and type_name_of_expr ctx e : string option =
  let enum_of v = match Hashtbl.find_opt g_variant v with Some (en, _, _) -> Some en | None -> None in
  match e with
  | Ident n when Hashtbl.mem g_variant n && not (Hashtbl.mem ctx.slots n) -> enum_of n
  | Ident n -> Hashtbl.find_opt ctx.locals_ty n
  | Field (b, f) | SafeField (b, f) ->
    (match type_name_of_expr ctx b with
     | Some st ->
       (match Hashtbl.find_opt g_struct_fields st with
        | Some fields ->
          (match List.find_opt (fun (n, _, _) -> n = f) fields with
           | Some (_, _, fty) -> Some fty
           | None -> None)
        | None -> None)
     | None -> None)
  | Call (Ident v, _) when Hashtbl.mem g_variant v -> enum_of v
  | Call (Ident n, _) when Hashtbl.mem g_struct_size n -> Some n
  | Call (Ident ("concat" | "substr" | "intToStr" | "readFile"), _) -> Some "String"
  | Call (Ident n, _) -> Hashtbl.find_opt g_fun_ret n
  | StringLit _ -> Some "String"
  | _ -> None

(* enum variant construction: box {tag @ 0, payload0 @ 8, ...}; ptr in x0 *)
and gen_variant_new ctx variant args =
  let _, tag, _ = Hashtbl.find g_variant variant in
  let n = List.length args in
  load_imm ctx 0 (8 + (n * 8));
  emit ctx (Bl "_malloc");           (* ptr -> x0 *)
  push ctx;
  load_imm ctx 0 tag;                (* tag -> x0 *)
  emit ctx (LdrSp 1);
  emit ctx (StrO (0, 1, 0));         (* [ptr] = tag *)
  List.iteri
    (fun j arg ->
      gen_expr ctx arg.arg_val;      (* payload j -> x0 *)
      emit ctx (LdrSp 1);
      emit ctx (StrO (0, 1, 8 + (j * 8))))
    args;
  emit ctx (Pop 0)

(* test a single pattern against the subject (a ptr/int on the stack at [sp]);
   on mismatch branch to [fail]; on match, bind any pattern variables. *)
and test_and_bind ctx pat ~fail =
  match pat with
  | PWild -> ()
  | PBind name -> emit ctx (LdrSp 0); st_fp ctx 0 (slot ctx name)
  | PLitInt n -> emit ctx (LdrSp 0); load_imm ctx 1 n; emit ctx (Cmp (0, 1)); emit ctx (Bcond ("ne", fail))
  | PLitBool b ->
    emit ctx (LdrSp 0); load_imm ctx 1 (if b then 1 else 0);
    emit ctx (Cmp (0, 1)); emit ctx (Bcond ("ne", fail))
  | PLitChar c -> emit ctx (LdrSp 0); load_imm ctx 1 c; emit ctx (Cmp (0, 1)); emit ctx (Bcond ("ne", fail))
  | PPath path ->
    let v = List.nth path (List.length path - 1) in
    (match Hashtbl.find_opt g_variant v with
     | Some (_, tag, _) ->
       emit ctx (LdrSp 0); emit ctx (LdrO (0, 0, 0));
       load_imm ctx 1 tag; emit ctx (Cmp (0, 1)); emit ctx (Bcond ("ne", fail))
     | None -> raise (Codegen_error (spf "unknown variant `%s` in pattern" v)))
  | PIs (t, false) ->
    let v = tyname t in
    (match Hashtbl.find_opt g_variant v with
     | Some (_, tag, _) ->
       emit ctx (LdrSp 0); emit ctx (LdrO (0, 0, 0));
       load_imm ctx 1 tag; emit ctx (Cmp (0, 1)); emit ctx (Bcond ("ne", fail))
     | None -> raise (Codegen_error (spf "`is %s`: not an enum variant (codegen)" v)))
  | PCtor (path, CPPos subpats) ->
    let v = List.nth path (List.length path - 1) in
    let _, tag, ptypes =
      match Hashtbl.find_opt g_variant v with
      | Some x -> x
      | None -> raise (Codegen_error (spf "unknown variant `%s` in pattern" v))
    in
    emit ctx (LdrSp 0);                (* ptr -> x0 *)
    emit ctx (LdrO (1, 0, 0));         (* tag -> x1 *)
    load_imm ctx 2 tag;
    emit ctx (Cmp (1, 2));
    emit ctx (Bcond ("ne", fail));
    List.iteri
      (fun j sp ->
        match sp with
        | PWild -> ()
        | PBind name ->
          emit ctx (LdrO (1, 0, 8 + (j * 8)));
          st_fp ctx 1 (slot ctx name);
          (match List.nth_opt ptypes j with
           | Some ty when ty <> "" -> Hashtbl.replace ctx.locals_ty name ty
           | _ -> ())
        | _ -> raise (Codegen_error "nested payload patterns not yet in codegen"))
      subpats
  | _ -> raise (Codegen_error "pattern not in the codegen subset")

and gen_when ctx subject arms =
  let l = fresh () in
  let lend = spf "Lwend_%d" l in
  match subject with
  | Some ws ->
    gen_expr ctx ws.ws_expr;           (* subject -> x0 *)
    push ctx;                          (* subject on the stack *)
    (match ws.ws_bind with
     | Some n -> emit ctx (LdrSp 0); st_fp ctx 0 (slot ctx n)
     | None -> ());
    List.iteri
      (fun i arm ->
        let lnext = spf "Lwn_%d_%d" l i in
        (match arm.wa_lhs with
         | LhsElse -> ()
         | LhsPatterns [ p ] -> test_and_bind ctx p ~fail:lnext
         | LhsPatterns _ -> raise (Codegen_error "or-patterns not yet in codegen")
         | LhsCond _ -> raise (Codegen_error "condition arm with a when-subject"));
        (match arm.wa_guard with
         | Some g -> gen_expr ctx g; emit ctx (Cbz (0, lnext))
         | None -> ());
        emit ctx (SpAdd 16);           (* matched: pop subject *)
        gen_expr ctx arm.wa_body;
        emit ctx (B lend);
        emit ctx (Label lnext))
      arms;
    emit ctx (SpAdd 16);               (* fell through (non-exhaustive) *)
    emit ctx (MovZero 0);
    emit ctx (Label lend)
  | None ->
    List.iteri
      (fun i arm ->
        let lnext = spf "Lwn_%d_%d" l i in
        (match arm.wa_lhs with
         | LhsElse -> ()
         | LhsCond c -> gen_expr ctx c; emit ctx (Cbz (0, lnext))
         | LhsPatterns _ -> raise (Codegen_error "pattern arm in a subject-less when"));
        gen_expr ctx arm.wa_body;
        emit ctx (B lend);
        emit ctx (Label lnext))
      arms;
    emit ctx (MovZero 0);
    emit ctx (Label lend)

let rec collect_locals acc e =
  match e with
  | Block (stmts, result) ->
    let acc = List.fold_left collect_locals_stmt acc stmts in
    (match result with Some e -> collect_locals acc e | None -> acc)
  | Binary (_, a, b) -> collect_locals (collect_locals acc a) b
  | Unary (_, a) | EReturn (Some a) -> collect_locals acc a
  | Call (_, args) -> List.fold_left (fun a arg -> collect_locals a arg.arg_val) acc args
  | If (c, t, eo) ->
    let acc = collect_locals (collect_locals acc c) t in
    (match eo with Some e -> collect_locals acc e | None -> acc)
  | When (subject, arms) ->
    let acc =
      match subject with
      | Some ws ->
        let acc = match ws.ws_bind with Some n -> n :: acc | None -> acc in
        collect_locals acc ws.ws_expr
      | None -> acc
    in
    List.fold_left
      (fun acc arm ->
        let acc =
          match arm.wa_lhs with
          | LhsPatterns pats -> List.fold_left collect_pattern_binds acc pats
          | LhsCond c -> collect_locals acc c
          | LhsElse -> acc
        in
        let acc = match arm.wa_guard with Some g -> collect_locals acc g | None -> acc in
        collect_locals acc arm.wa_body)
      acc arms
  | Field (b, _) | SafeField (b, _) | Static (b, _) | NotNull b | TypeApp (b, _) ->
    collect_locals acc b
  | Elvis (a, b) | Index (a, b) -> collect_locals (collect_locals acc a) b
  | Interp parts ->
    List.fold_left (fun a p -> match p with IExpr e -> collect_locals a e | ILit _ -> a) acc parts
  | _ -> acc

and collect_pattern_binds acc pat =
  match pat with
  | PBind n -> n :: acc
  | PCtor (_, CPPos ps) -> List.fold_left collect_pattern_binds acc ps
  | PCtor (_, CPRecord (fs, _)) ->
    List.fold_left
      (fun a f -> match f.rf_pat with Some p -> collect_pattern_binds a p | None -> f.rf_name :: a)
      acc fs
  | _ -> acc

and collect_locals_stmt acc s =
  match s with
  | SLet { name; init; _ } -> collect_locals (name :: acc) init
  | SExpr e | SReturn (Some e) -> collect_locals acc e
  | SAssign (_, e) -> collect_locals acc e
  | SWhile (c, b) -> collect_locals (collect_locals acc c) b
  | SFor { var; iter; body } -> collect_locals (collect_locals (var :: acc) iter) body
  | _ -> acc

let gen_fun code fd =
  match fd.fn_body with
  | None -> ()
  | Some body ->
    let name = fd.fn_name in
    let params = List.map (fun p -> p.pname) fd.fn_params in
    let locals = List.rev (collect_locals [] body) in
    let names = params @ List.filter (fun n -> not (List.mem n params)) locals in
    let slots = Hashtbl.create 16 in
    List.iteri (fun i n -> Hashtbl.replace slots n (8 * (i + 1))) names;
    let frame = align16 (8 * List.length names) in
    let epi = spf "Lepi_%s" name in
    let ctx = { code; slots; epi; locals_ty = Hashtbl.create 16 } in
    List.iter (fun p -> Hashtbl.replace ctx.locals_ty p.pname (tyname p.pty)) fd.fn_params;
    emit ctx (Raw (spf "\t.globl _%s\n\t.p2align 2\n" name));
    emit ctx (Label ("_" ^ name));
    emit ctx StpFp;
    emit ctx MovFpSp;
    if frame > 0 then emit ctx (SpSub frame);
    List.iteri
      (fun i _ -> if i < List.length params then st_fp ctx i (8 * (i + 1)))
      params;
    gen_expr ctx body;
    emit ctx (Label epi);
    if frame > 0 then emit ctx (SpAdd frame);
    emit ctx LdpFp;
    emit ctx Ret;
    emit ctx (Raw "\n")

(* Build the full program IR (the same instruction stream the text emitter
   renders) — exposed so the encoder / Mach-O writer can consume it. *)
(* escape a cstring's bytes (which include a trailing NUL) for a `.asciz` line;
   .asciz appends the NUL implicitly, so drop it. *)
let asciz_escape s =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
      match c with
      | '\000' -> ()
      | '\n' -> Buffer.add_string b "\\n"
      | '\t' -> Buffer.add_string b "\\t"
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let program_instrs (prog : program) : instr list =
  label_counter := 0;
  Hashtbl.reset string_labels;
  user_strings := [];
  string_ctr := 0;
  build_types prog;
  let code = ref [] in
  let push_raw s = code := Raw s :: !code in
  push_raw "\t.text\n";
  List.iter (function FunDecl fd -> gen_fun code fd | _ -> ()) prog;
  push_raw "\t.section __TEXT,__cstring,cstring_literals\n";
  List.iter
    (fun (label, bytes) -> push_raw (spf "%s:\n\t.asciz \"%s\"\n" label (asciz_escape bytes)))
    (all_cstrings ());
  List.rev !code

(* Returns the raw __cstring bytes and each label's byte offset within it —
   built-in printf formats first, then interned user string literals. Must be
   called after program_instrs has populated the user-string table. *)
let cstring_section () : string * (string * int) list =
  let buf = Buffer.create 16 in
  let labels =
    List.map
      (fun (name, bytes) ->
        let off = Buffer.length buf in
        Buffer.add_string buf bytes;
        (name, off))
      (all_cstrings ())
  in
  (Buffer.contents buf, labels)

let emit_program (prog : program) : string =
  let instrs = program_instrs prog in
  let buf = Buffer.create 1024 in
  List.iter (fun i -> Buffer.add_string buf (print_instr i)) instrs;
  Buffer.contents buf
