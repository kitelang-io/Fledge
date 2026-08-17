(* Mach-O writers for AArch64 — Fledge's own object writer AND its own linker.

   Two entry points:
     - write_object    : a linkable MH_OBJECT (.o) — kept for `kitec obj`.
     - write_executable: a fully-linked, directly-runnable MH_EXECUTE. This is
       Fledge's own minimal LINKER (no ld, no clang): it lays the segments out at
       their runtime vm addresses, resolves the intra-image pc-relative branches
       and adrp/add to our own __cstring, sets LC_MAIN's entry, emits dyld
       chained-fixups bindings for external imports (printf), and ad-hoc
       code-signs. `kitec run`/`kitec exe` use it; only dyld touches the result
       at runtime.

   The MH_OBJECT writer below handles a defined external function `_main` with
   cross-symbol relocations: exactly enough to pack

       fun main(): Int { return 2 + 3 * 4 }

   into a linkable object. Layout and every struct field/size/flag were derived
   by diffing against `clang -c -arch arm64` of the same assembly (otool -l,
   otool -rv, xxd). The file contains:

     mach_header_64
     LC_SEGMENT_64  (one anonymous segment holding a __text section in __TEXT)
     LC_BUILD_VERSION
     LC_SYMTAB
     LC_DYSYMTAB
     <__text bytes>
     <nlist_64 symbol table>  (one entry: _main, N_SECT|N_EXT, n_sect=1, value=0)
     <string table>

   Later increments widen this to a __cstring section, local symbols, and the
   ARM64_RELOC_* relocations that `bl _printf` / `adrp`+`add` need. *)

let byte_buf () = Buffer.create 1024

let u8 b v = Buffer.add_char b (Char.chr (v land 0xff))

let u16 b v =
  u8 b v;
  u8 b (v asr 8)

let u32 b v =
  u8 b v;
  u8 b (v asr 8);
  u8 b (v asr 16);
  u8 b (v asr 24)

(* 64-bit little-endian; OCaml native int is 63-bit but our values are small. *)
let u64 b v =
  u32 b v;
  u32 b (v asr 32)

(* fixed-size, NUL-padded field (used for segname/sectname, 16 bytes) *)
let fixed b n s =
  let len = String.length s in
  for i = 0 to n - 1 do
    u8 b (if i < len then Char.code s.[i] else 0)
  done

(* ---- Mach-O / load-command constants (from <mach-o/loader.h>) ---- *)
let mh_magic_64 = 0xFEEDFACF
let cpu_type_arm64 = 0x0100000C
let cpu_subtype_arm64_all = 0x00000000
let mh_object = 0x1
let lc_segment_64 = 0x19
let lc_build_version = 0x32
let lc_symtab = 0x2
let lc_dysymtab = 0xB

(* section __text attributes: S_ATTR_PURE_INSTRUCTIONS|S_ATTR_SOME_INSTRUCTIONS *)
let s_text_flags = 0x80000400

(* nlist_64 n_type bits *)
let n_ext = 0x01
let n_sect = 0x0E
let n_undf = 0x00

(* align n up to the next multiple of 8 *)
let align8 n = (n + 7) land lnot 7

(* Write a Mach-O object for one function `_main` whose machine code is [text]
   (an array of 32-bit little-endian words). No relocations. *)
let write_main_object ~(path : string) ~(text : int array) : unit =
  let text_size = 4 * Array.length text in

  (* load command sizes *)
  let seg_cmdsize = 72 + 80 (* segment header + one section_64 *) in
  let build_cmdsize = 24 in
  let symtab_cmdsize = 24 in
  let dysymtab_cmdsize = 80 in
  let sizeofcmds = seg_cmdsize + build_cmdsize + symtab_cmdsize + dysymtab_cmdsize in
  let ncmds = 4 in

  let header_size = 32 in
  let text_off = header_size + sizeofcmds in
  let symoff = text_off + text_size in
  let nsyms = 1 in
  let stroff = symoff + (16 * nsyms) in

  (* string table: leading NUL, then "_main\0", padded to 8 bytes *)
  let strtab = byte_buf () in
  u8 strtab 0;
  String.iter (fun c -> u8 strtab (Char.code c)) "_main";
  u8 strtab 0;
  while Buffer.length strtab land 7 <> 0 do
    u8 strtab 0
  done;
  let strsize = Buffer.length strtab in

  let b = byte_buf () in

  (* ---- mach_header_64 ---- *)
  u32 b mh_magic_64;
  u32 b cpu_type_arm64;
  u32 b cpu_subtype_arm64_all;
  u32 b mh_object;
  u32 b ncmds;
  u32 b sizeofcmds;
  u32 b 0;              (* flags *)
  u32 b 0;              (* reserved *)

  (* ---- LC_SEGMENT_64 ---- *)
  u32 b lc_segment_64;
  u32 b seg_cmdsize;
  fixed b 16 "";        (* segname (empty for MH_OBJECT) *)
  u64 b 0;              (* vmaddr *)
  u64 b text_size;      (* vmsize *)
  u64 b text_off;       (* fileoff *)
  u64 b text_size;      (* filesize *)
  u32 b 0x7;            (* maxprot rwx *)
  u32 b 0x7;            (* initprot rwx *)
  u32 b 1;              (* nsects *)
  u32 b 0;              (* flags *)

  (* section_64: __text,__TEXT *)
  fixed b 16 "__text";
  fixed b 16 "__TEXT";
  u64 b 0;              (* addr *)
  u64 b text_size;      (* size *)
  u32 b text_off;       (* offset *)
  u32 b 2;              (* align = 2^2 = 4 *)
  u32 b 0;              (* reloff *)
  u32 b 0;              (* nreloc *)
  u32 b s_text_flags;   (* flags *)
  u32 b 0;              (* reserved1 *)
  u32 b 0;              (* reserved2 *)
  u32 b 0;              (* reserved3 *)

  (* ---- LC_BUILD_VERSION ---- *)
  u32 b lc_build_version;
  u32 b build_cmdsize;
  u32 b 1;              (* platform = PLATFORM_MACOS *)
  u32 b 0x000B0000;     (* minos = 11.0.0 *)
  u32 b 0x000B0000;     (* sdk   = 11.0.0 *)
  u32 b 0;              (* ntools *)

  (* ---- LC_SYMTAB ---- *)
  u32 b lc_symtab;
  u32 b symtab_cmdsize;
  u32 b symoff;
  u32 b nsyms;
  u32 b stroff;
  u32 b strsize;

  (* ---- LC_DYSYMTAB ---- *)
  u32 b lc_dysymtab;
  u32 b dysymtab_cmdsize;
  u32 b 0;              (* ilocalsym *)
  u32 b 0;              (* nlocalsym *)
  u32 b 0;              (* iextdefsym *)
  u32 b 1;              (* nextdefsym (_main) *)
  u32 b 1;              (* iundefsym *)
  u32 b 0;              (* nundefsym *)
  u32 b 0; u32 b 0;     (* tocoff / ntoc *)
  u32 b 0; u32 b 0;     (* modtaboff / nmodtab *)
  u32 b 0; u32 b 0;     (* extrefsymoff / nextrefsyms *)
  u32 b 0; u32 b 0;     (* indirectsymoff / nindirectsyms *)
  u32 b 0; u32 b 0;     (* extreloff / nextrel *)
  u32 b 0; u32 b 0;     (* locreloff / nlocrel *)

  (* ---- section data: __text ---- *)
  Array.iter (fun w -> u32 b w) text;

  (* ---- symbol table (nlist_64): _main ---- *)
  u32 b 1;              (* n_strx -> "_main" (offset 1 in strtab) *)
  u8 b (n_sect lor n_ext); (* n_type = N_SECT|N_EXT = 0x0F *)
  u8 b 1;               (* n_sect = 1 (__text) *)
  u16 b 0;              (* n_desc *)
  u64 b 0;              (* n_value = 0 *)

  (* ---- string table ---- *)
  Buffer.add_buffer b strtab;

  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
      Buffer.output_buffer oc b)

(* =====================================================================
   SHA-256 (needed for the ad-hoc code signature: Apple Silicon refuses to
   exec an unsigned arm64 binary — SIGKILL. Pure OCaml, 32-bit words held in
   native ints masked to 0xFFFFFFFF; input is any string, output is a raw
   32-byte digest string.)
   ===================================================================== *)
module Sha256 = struct
  let m32 = 0xFFFFFFFF
  let ( +% ) a b = (a + b) land m32
  let rotr x n = (((x lsr n) lor (x lsl (32 - n)))) land m32
  let shr x n = (x lsr n) land m32

  let k =
    [| 0x428a2f98;0x71374491;0xb5c0fbcf;0xe9b5dba5;0x3956c25b;0x59f111f1;
       0x923f82a4;0xab1c5ed5;0xd807aa98;0x12835b01;0x243185be;0x550c7dc3;
       0x72be5d74;0x80deb1fe;0x9bdc06a7;0xc19bf174;0xe49b69c1;0xefbe4786;
       0x0fc19dc6;0x240ca1cc;0x2de92c6f;0x4a7484aa;0x5cb0a9dc;0x76f988da;
       0x983e5152;0xa831c66d;0xb00327c8;0xbf597fc7;0xc6e00bf3;0xd5a79147;
       0x06ca6351;0x14292967;0x27b70a85;0x2e1b2138;0x4d2c6dfc;0x53380d13;
       0x650a7354;0x766a0abb;0x81c2c92e;0x92722c85;0xa2bfe8a1;0xa81a664b;
       0xc24b8b70;0xc76c51a3;0xd192e819;0xd6990624;0xf40e3585;0x106aa070;
       0x19a4c116;0x1e376c08;0x2748774c;0x34b0bcb5;0x391c0cb3;0x4ed8aa4a;
       0x5b9cca4f;0x682e6ff3;0x748f82ee;0x78a5636f;0x84c87814;0x8cc70208;
       0x90befffa;0xa4506ceb;0xbef9a3f7;0xc67178f2 |]

  let digest (msg : string) : string =
    let ml = String.length msg in
    (* padded message: msg ++ 0x80 ++ 0x00* ++ 64-bit big-endian bit length *)
    let bitlen = ml * 8 in
    let padlen =
      let r = (ml + 1) mod 64 in
      if r <= 56 then 56 - r else 120 - r
    in
    let total = ml + 1 + padlen + 8 in
    let m = Bytes.make total '\000' in
    Bytes.blit_string msg 0 m 0 ml;
    Bytes.set m ml '\x80';
    for i = 0 to 7 do
      Bytes.set m (total - 1 - i)
        (Char.chr ((bitlen lsr (8 * i)) land 0xff))
    done;
    let h = [| 0x6a09e667;0xbb67ae85;0x3c6ef372;0xa54ff53a;
               0x510e527f;0x9b05688c;0x1f83d9ab;0x5be0cd19 |] in
    let w = Array.make 64 0 in
    let nblocks = total / 64 in
    for b = 0 to nblocks - 1 do
      let base = b * 64 in
      for t = 0 to 15 do
        let o = base + t * 4 in
        w.(t) <-
          ((Char.code (Bytes.get m o) lsl 24)
           lor (Char.code (Bytes.get m (o + 1)) lsl 16)
           lor (Char.code (Bytes.get m (o + 2)) lsl 8)
           lor Char.code (Bytes.get m (o + 3))) land m32
      done;
      for t = 16 to 63 do
        let s0 = rotr w.(t-15) 7 lxor rotr w.(t-15) 18 lxor shr w.(t-15) 3 in
        let s1 = rotr w.(t-2) 17 lxor rotr w.(t-2) 19 lxor shr w.(t-2) 10 in
        w.(t) <- (w.(t-16) +% s0 +% w.(t-7) +% s1)
      done;
      let a = ref h.(0) and bb = ref h.(1) and c = ref h.(2) and d = ref h.(3)
      and e = ref h.(4) and f = ref h.(5) and g = ref h.(6) and hh = ref h.(7) in
      for t = 0 to 63 do
        let s1 = rotr !e 6 lxor rotr !e 11 lxor rotr !e 25 in
        let ch = ((!e land !f) lxor ((lnot !e) land !g)) land m32 in
        let t1 = !hh +% s1 +% ch +% k.(t) +% w.(t) in
        let s0 = rotr !a 2 lxor rotr !a 13 lxor rotr !a 22 in
        let maj = (!a land !bb) lxor (!a land !c) lxor (!bb land !c) in
        let t2 = s0 +% maj in
        hh := !g; g := !f; f := !e; e := (!d +% t1);
        d := !c; c := !bb; bb := !a; a := (t1 +% t2)
      done;
      h.(0) <- h.(0) +% !a; h.(1) <- h.(1) +% !bb; h.(2) <- h.(2) +% !c;
      h.(3) <- h.(3) +% !d; h.(4) <- h.(4) +% !e; h.(5) <- h.(5) +% !f;
      h.(6) <- h.(6) +% !g; h.(7) <- h.(7) +% !hh
    done;
    let out = Bytes.create 32 in
    for i = 0 to 7 do
      Bytes.set out (i*4)   (Char.chr ((h.(i) lsr 24) land 0xff));
      Bytes.set out (i*4+1) (Char.chr ((h.(i) lsr 16) land 0xff));
      Bytes.set out (i*4+2) (Char.chr ((h.(i) lsr 8) land 0xff));
      Bytes.set out (i*4+3) (Char.chr (h.(i) land 0xff))
    done;
    Bytes.to_string out
end

(* section __cstring flags: S_CSTRING_LITERALS *)
let s_cstring_flags = 0x00000002

(* A relocation the writer must emit. [ro_off] is the byte offset of the target
   instruction word within __text; [ro_sym] the referenced symbol name (a
   __cstring label for PAGE21/PAGEOFF12, a function name — with its leading '_' —
   for BRANCH26). *)
type reloc_kind = Reloc_branch26 | Reloc_page21 | Reloc_pageoff12
type reloc_entry = { ro_off : int; ro_sym : string; ro_kind : reloc_kind }

(* Write a Mach-O object with a __text section and a __cstring section, plus
   ARM64_RELOC_BRANCH26 (bl _sym), ARM64_RELOC_PAGE21 (adrp Xd,L@PAGE) and
   ARM64_RELOC_PAGEOFF12 (add Xd,Xn,L@PAGEOFF) relocations.

   [text]           machine-code words (in order) for the whole __text section.
   [cstring]        raw bytes of the __cstring section.
   [cstring_labels] (label, byte-offset within __cstring) for each literal.
   [defined_syms]   (name, byte-offset in __text) per defined function.
   [relocs]         one entry per cross-symbol reference.

   Symbol-table order (required by ld / matched to clang -c -arch arm64, verified
   via otool -l/-rv, xxd): local symbols first (the __cstring labels that any
   relocation references — N_SECT into __cstring), then defined external
   functions (N_SECT|N_EXT into __text), then undefined externals (N_UNDF|N_EXT,
   e.g. _printf). A relocation's r_symbolnum is the target's index in that table;
   PAGE21/PAGEOFF12 target the local __cstring symbol, BRANCH26 the function. *)
let write_object ~(path : string) ~(text : int array) ~(cstring : string)
    ~(cstring_labels : (string * int) list)
    ~(defined_syms : (string * int) list) ~(relocs : reloc_entry list) : unit =
  let text_size = 4 * Array.length text in
  let cstring_size = String.length cstring in
  let cstring_addr = text_size in   (* __cstring follows __text; align 1 *)

  let defined_names = List.map fst defined_syms in
  let cstr_label_off = Hashtbl.create 16 in
  List.iter (fun (n, o) -> Hashtbl.replace cstr_label_off n o) cstring_labels;

  (* Partition reloc target symbols into: local __cstring labels, and undefined
     externals (targets that are neither a defined function nor a cstring label),
     each in first-appearance order. *)
  let is_defined n = List.mem n defined_names in
  let is_cstring n = Hashtbl.mem cstr_label_off n in
  let locals =
    let seen = Hashtbl.create 16 and acc = ref [] in
    List.iter
      (fun r ->
        if is_cstring r.ro_sym && not (Hashtbl.mem seen r.ro_sym) then begin
          Hashtbl.replace seen r.ro_sym ();
          acc := r.ro_sym :: !acc
        end)
      relocs;
    List.rev !acc
  in
  let undefined =
    let seen = Hashtbl.create 16 and acc = ref [] in
    List.iter
      (fun r ->
        if (not (is_defined r.ro_sym)) && (not (is_cstring r.ro_sym))
           && not (Hashtbl.mem seen r.ro_sym) then begin
          Hashtbl.replace seen r.ro_sym ();
          acc := r.ro_sym :: !acc
        end)
      relocs;
    List.rev !acc
  in

  (* symtab order: locals, then defined externals, then undefined externals. *)
  let ordered = locals @ defined_names @ undefined in
  let sym_index = Hashtbl.create 16 in
  List.iteri (fun i n -> Hashtbl.replace sym_index n i) ordered;
  let nlocal = List.length locals in
  let ndef = List.length defined_names in
  let nundef = List.length undefined in
  let nsyms = nlocal + ndef + nundef in
  let nreloc = List.length relocs in

  (* load command sizes (one segment, two sections: __text + __cstring) *)
  let seg_cmdsize = 72 + 80 + 80 in
  let build_cmdsize = 24 in
  let symtab_cmdsize = 24 in
  let dysymtab_cmdsize = 80 in
  let sizeofcmds = seg_cmdsize + build_cmdsize + symtab_cmdsize + dysymtab_cmdsize in
  let ncmds = 4 in

  let header_size = 32 in
  let text_off = header_size + sizeofcmds in
  let cstring_off = text_off + text_size in     (* align 1: no padding *)
  let data_end = align8 (cstring_off + cstring_size) in
  let reloff = if nreloc > 0 then data_end else 0 in
  let symoff = data_end + (8 * nreloc) in
  let stroff = symoff + (16 * nsyms) in

  (* string table: leading NUL, then each symbol name NUL-terminated, padded 8 *)
  let strtab = byte_buf () in
  let str_off = Hashtbl.create 16 in
  u8 strtab 0;
  List.iter
    (fun name ->
      Hashtbl.replace str_off name (Buffer.length strtab);
      String.iter (fun c -> u8 strtab (Char.code c)) name;
      u8 strtab 0)
    ordered;
  while Buffer.length strtab land 7 <> 0 do
    u8 strtab 0
  done;
  let strsize = Buffer.length strtab in

  let b = byte_buf () in

  (* ---- mach_header_64 ---- *)
  u32 b mh_magic_64;
  u32 b cpu_type_arm64;
  u32 b cpu_subtype_arm64_all;
  u32 b mh_object;
  u32 b ncmds;
  u32 b sizeofcmds;
  u32 b 0;
  u32 b 0;

  (* ---- LC_SEGMENT_64 ---- *)
  u32 b lc_segment_64;
  u32 b seg_cmdsize;
  fixed b 16 "";
  u64 b 0;                        (* vmaddr *)
  u64 b (text_size + cstring_size); (* vmsize *)
  u64 b text_off;                 (* fileoff *)
  u64 b (text_size + cstring_size); (* filesize *)
  u32 b 0x7;
  u32 b 0x7;
  u32 b 2;                        (* nsects *)
  u32 b 0;

  (* section_64: __text,__TEXT *)
  fixed b 16 "__text";
  fixed b 16 "__TEXT";
  u64 b 0;                        (* addr *)
  u64 b text_size;                (* size *)
  u32 b text_off;                 (* offset *)
  u32 b 2;                        (* align 2^2 = 4 *)
  u32 b reloff;
  u32 b nreloc;
  u32 b s_text_flags;
  u32 b 0;
  u32 b 0;
  u32 b 0;

  (* section_64: __cstring,__TEXT *)
  fixed b 16 "__cstring";
  fixed b 16 "__TEXT";
  u64 b cstring_addr;             (* addr *)
  u64 b cstring_size;             (* size *)
  u32 b cstring_off;              (* offset *)
  u32 b 0;                        (* align 2^0 = 1 *)
  u32 b 0;                        (* reloff *)
  u32 b 0;                        (* nreloc *)
  u32 b s_cstring_flags;
  u32 b 0;
  u32 b 0;
  u32 b 0;

  (* ---- LC_BUILD_VERSION ---- *)
  u32 b lc_build_version;
  u32 b build_cmdsize;
  u32 b 1;
  u32 b 0x000B0000;
  u32 b 0x000B0000;
  u32 b 0;

  (* ---- LC_SYMTAB ---- *)
  u32 b lc_symtab;
  u32 b symtab_cmdsize;
  u32 b symoff;
  u32 b nsyms;
  u32 b stroff;
  u32 b strsize;

  (* ---- LC_DYSYMTAB ---- *)
  u32 b lc_dysymtab;
  u32 b dysymtab_cmdsize;
  u32 b 0;              (* ilocalsym *)
  u32 b nlocal;         (* nlocalsym *)
  u32 b nlocal;         (* iextdefsym *)
  u32 b ndef;           (* nextdefsym *)
  u32 b (nlocal + ndef);(* iundefsym *)
  u32 b nundef;         (* nundefsym *)
  u32 b 0; u32 b 0;
  u32 b 0; u32 b 0;
  u32 b 0; u32 b 0;
  u32 b 0; u32 b 0;
  u32 b 0; u32 b 0;
  u32 b 0; u32 b 0;

  (* ---- section data: __text ---- *)
  Array.iter (fun w -> u32 b w) text;
  (* ---- section data: __cstring ---- *)
  String.iter (fun c -> u8 b (Char.code c)) cstring;
  (* pad to 8 before relocations / symtab *)
  while Buffer.length b land 7 <> 0 do
    u8 b 0
  done;

  (* ---- relocation entries ---- *)
  (* clang emits relocs in descending r_address order; match it. *)
  let relocs_sorted =
    List.sort (fun a b -> compare b.ro_off a.ro_off) relocs
  in
  List.iter
    (fun r ->
      let idx = Hashtbl.find sym_index r.ro_sym in
      u32 b r.ro_off;
      (* packed 32-bit little-endian bitfield:
         symbolnum:24 | pcrel:1 | length:2 | extern:1 | type:4 *)
      let pcrel, len, typ =
        match r.ro_kind with
        | Reloc_branch26 -> (1, 2, 2)   (* ARM64_RELOC_BRANCH26 *)
        | Reloc_page21 -> (1, 2, 3)     (* ARM64_RELOC_PAGE21 *)
        | Reloc_pageoff12 -> (0, 2, 4)  (* ARM64_RELOC_PAGEOFF12 *)
      in
      let packed =
        (idx land 0xffffff)
        lor (pcrel lsl 24)
        lor (len lsl 25)
        lor (1 lsl 27)                  (* r_extern = 1 *)
        lor (typ lsl 28)
      in
      u32 b packed)
    relocs_sorted;

  (* ---- symbol table (nlist_64) ---- *)
  (* locals: __cstring labels (N_SECT into __cstring, n_sect=2) *)
  List.iter
    (fun name ->
      u32 b (Hashtbl.find str_off name);
      u8 b n_sect;                       (* 0x0E, local (no N_EXT) *)
      u8 b 2;                            (* n_sect = 2 (__cstring) *)
      u16 b 0;
      u64 b (cstring_addr + Hashtbl.find cstr_label_off name))
    locals;
  (* defined external functions (N_SECT|N_EXT into __text, n_sect=1) *)
  List.iter
    (fun (name, value) ->
      u32 b (Hashtbl.find str_off name);
      u8 b (n_sect lor n_ext);   (* 0x0F *)
      u8 b 1;                    (* n_sect = 1 (__text) *)
      u16 b 0;
      u64 b value)
    defined_syms;
  (* undefined externals (N_UNDF|N_EXT) *)
  List.iter
    (fun name ->
      u32 b (Hashtbl.find str_off name);
      u8 b (n_undf lor n_ext);   (* 0x01 *)
      u8 b 0;                    (* n_sect = 0 *)
      u16 b 0;
      u64 b 0)
    undefined;

  (* ---- string table ---- *)
  Buffer.add_buffer b strtab;

  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
      Buffer.output_buffer oc b)

(* =====================================================================
   Self-linked MH_EXECUTE writer (no ld, no clang).

   Produces a directly-runnable Mach-O executable for a program whose only
   cross-symbol references are intra-image `bl` calls between its own defined
   functions (resolved here to final PC-relative displacements) and, optionally,
   adrp/add references to its own __cstring literals. External symbols (e.g.
   _printf) are NOT handled here — that is a later increment.

   Layout (all sizes/vmaddrs/fileoffs derived by reference-diffing an ld-linked
   executable via `otool -l` + `xxd`):

     __PAGEZERO  vmaddr 0, vmsize 0x100000000, no file data
     __TEXT      vmaddr 0x100000000, fileoff 0 -> mach_header + load commands +
                 __text + __cstring, r-x, page(0x4000)-aligned filesize
     __LINKEDIT  chained-fixups(binds nothing) + symtab + strtab + ad-hoc
                 code signature (mandatory on Apple Silicon)

   Load commands: LC_SEGMENT_64 x3, LC_DYLD_CHAINED_FIXUPS, LC_DYLD_EXPORTS_TRIE
   (empty), LC_SYMTAB, LC_DYSYMTAB, LC_LOAD_DYLINKER, LC_UUID, LC_BUILD_VERSION,
   LC_MAIN, LC_LOAD_DYLIB(libSystem), LC_CODE_SIGNATURE. *)

let lc_req_dyld = 0x80000000
let lc_dyld_chained_fixups = lc_req_dyld lor 0x34
let lc_dyld_exports_trie = lc_req_dyld lor 0x33
let lc_symtab2 = 0x2
let lc_load_dylinker = 0xe
let lc_uuid = 0x1b
let lc_main = lc_req_dyld lor 0x28
let lc_load_dylib = 0xc
let lc_code_signature = 0x1d

let align_up n a = (n + a - 1) / a * a

(* big-endian writers (the code-signature blobs are big-endian) *)
let be16 b v = u8 b (v asr 8); u8 b v
let be32 b v = be16 b (v asr 16); be16 b v
let be64 b v = be32 b (v asr 32); be32 b v

let write_executable ~(path : string) ~(text : int array) ~(cstring : string)
    ~(cstring_labels : (string * int) list)
    ~(defined_syms : (string * int) list) ~(relocs : reloc_entry list)
    ~(entry : string) ~(ident : string) : unit =
  let vmpage = 0x4000 in
  let text_seg_vmaddr = 0x100000000 in

  (* ---- external (undefined) symbols referenced by BRANCH26 relocations, in
     first-appearance order. Each gets a __stubs entry appended to __text and a
     __got slot bound to it by dyld via chained fixups. PAGE21/PAGEOFF12 must
     stay intra-image (our own __cstring). *)
  let dsym = Hashtbl.create 16 in
  List.iter (fun (n, o) -> Hashtbl.replace dsym n o) defined_syms;
  let externals =
    let seen = Hashtbl.create 8 and acc = ref [] in
    List.iter
      (fun r ->
        match r.ro_kind with
        | Reloc_branch26
          when (not (Hashtbl.mem dsym r.ro_sym))
               && not (Hashtbl.mem seen r.ro_sym) ->
          Hashtbl.replace seen r.ro_sym ();
          acc := r.ro_sym :: !acc
        | _ -> ())
      relocs;
    List.rev !acc
  in
  let nimp = List.length externals in
  let has_data = nimp > 0 in
  let ext_index = Hashtbl.create 8 in
  List.iteri (fun i n -> Hashtbl.replace ext_index n i) externals;

  (* ---- load-command sizes (fixed) ---- *)
  let cs_pagezero = 72 in
  let cs_textseg = 72 + (2 * 80) in
  let cs_dataconst = 72 + 80 in         (* only present when [has_data] *)
  let cs_linkedit = 72 in
  let cs_chained = 16 in
  let cs_exports = 16 in
  let cs_symtab = 24 in
  let cs_dysymtab = 80 in
  let cs_dylinker = 32 in
  let cs_uuid = 24 in
  let cs_buildver = 24 in
  let cs_main = 24 in
  let cs_dylib = 56 in
  let cs_codesig = 16 in
  let sizeofcmds =
    cs_pagezero + cs_textseg + (if has_data then cs_dataconst else 0)
    + cs_linkedit + cs_chained + cs_exports + cs_symtab
    + cs_dysymtab + cs_dylinker + cs_uuid + cs_buildver + cs_main + cs_dylib
    + cs_codesig
  in
  let ncmds = if has_data then 14 else 13 in
  let header_size = 32 in
  let lc_end = header_size + sizeofcmds in

  (* ---- __TEXT layout (stubs are appended to __text after the user code) ---- *)
  let text_off = align_up lc_end 16 in
  let user_text_size = 4 * Array.length text in
  let stubs_size = nimp * 12 in
  let text_size = user_text_size + stubs_size in
  let cstring_off = text_off + text_size in
  let cstring_size = String.length cstring in
  let text_content_end = cstring_off + cstring_size in
  let text_seg_filesize = align_up text_content_end vmpage in
  let text_vmaddr = text_seg_vmaddr + text_off in
  let cstring_vmaddr = text_seg_vmaddr + cstring_off in

  (* ---- __DATA_CONST / __got layout (present only when [has_data]) ---- *)
  let dataconst_fileoff = text_seg_filesize in
  let dataconst_vmaddr = text_seg_vmaddr + text_seg_filesize in
  let got_size = nimp * 8 in
  let dataconst_filesize = if has_data then align_up got_size vmpage else 0 in
  let dataconst_vmsize = dataconst_filesize in

  (* ---- resolve relocations into a private copy of the text words ---- *)
  let words = Array.copy text in
  let clbl = Hashtbl.create 16 in
  List.iter (fun (n, o) -> Hashtbl.replace clbl n o) cstring_labels;
  List.iter
    (fun r ->
      let idx = r.ro_off / 4 in
      match r.ro_kind with
      | Reloc_branch26 ->
        (match Hashtbl.find_opt dsym r.ro_sym with
         | Some target ->
           let disp = (target - r.ro_off) / 4 in
           words.(idx) <-
             (words.(idx) land (lnot 0x03FFFFFF)) lor (disp land 0x03FFFFFF)
         | None ->
           (match Hashtbl.find_opt ext_index r.ro_sym with
            | Some i ->
              (* branch to this symbol's stub (appended after the user code) *)
              let target = user_text_size + (i * 12) in
              let disp = (target - r.ro_off) / 4 in
              words.(idx) <-
                (words.(idx) land (lnot 0x03FFFFFF)) lor (disp land 0x03FFFFFF)
            | None ->
              failwith
                (Printf.sprintf
                   "write_executable: external symbol %s (BRANCH26) not supported"
                   r.ro_sym)))
      | Reloc_page21 ->
        (match Hashtbl.find_opt clbl r.ro_sym with
         | Some coff ->
           let target = cstring_vmaddr + coff in
           let pc = text_vmaddr + r.ro_off in
           let imm = (target asr 12) - (pc asr 12) in
           let immlo = imm land 0x3 and immhi = (imm asr 2) land 0x7ffff in
           words.(idx) <- words.(idx) lor (immlo lsl 29) lor (immhi lsl 5)
         | None ->
           failwith
             (Printf.sprintf "write_executable: external symbol %s (PAGE21)"
                r.ro_sym))
      | Reloc_pageoff12 ->
        (match Hashtbl.find_opt clbl r.ro_sym with
         | Some coff ->
           let target = cstring_vmaddr + coff in
           let imm12 = target land 0xfff in
           words.(idx) <- words.(idx) lor (imm12 lsl 10)
         | None ->
           failwith
             (Printf.sprintf "write_executable: external symbol %s (PAGEOFF12)"
                r.ro_sym)))
    relocs;

  (* ---- synthesize one stub per external symbol and append to __text.
     Each stub:  adrp x16, got_slot@PAGE ; ldr x16,[x16, got_slot@PAGEOFF] ; br x16 *)
  let stub_words = Array.make (nimp * 3) 0 in
  for i = 0 to nimp - 1 do
    let got_va = dataconst_vmaddr + (i * 8) in
    let stub_va = text_vmaddr + user_text_size + (i * 12) in
    let page_delta = (got_va asr 12) - (stub_va asr 12) in
    let immlo = page_delta land 0x3 and immhi = (page_delta asr 2) land 0x7ffff in
    stub_words.(i * 3) <- 0x90000000 lor (immlo lsl 29) lor (immhi lsl 5) lor 16;
    let off12 = got_va land 0xfff in
    stub_words.(i * 3 + 1) <-
      0xF9400000 lor ((off12 / 8) lsl 10) lor (16 lsl 5) lor 16;
    stub_words.(i * 3 + 2) <- 0xD61F0200 (* br x16 *)
  done;
  let words = Array.append words stub_words in

  (* ---- string table (leading NUL, name\0..., padded to 8) ---- *)
  let strtab = byte_buf () in
  let str_off = Hashtbl.create 16 in
  u8 strtab 0;
  List.iter
    (fun (name, _) ->
      Hashtbl.replace str_off name (Buffer.length strtab);
      String.iter (fun c -> u8 strtab (Char.code c)) name;
      u8 strtab 0)
    defined_syms;
  while Buffer.length strtab land 7 <> 0 do u8 strtab 0 done;
  let strsize = Buffer.length strtab in
  let nsyms = List.length defined_syms in

  (* ---- chained-fixups payload (built here so its exact size drives layout).
     No imports: a header that binds nothing (seg_count = 3). With imports: a
     header + starts_in_image + one starts_in_segment for __DATA_CONST + an
     imports table + a symbol string pool naming each external. *)
  let chained_payload =
    let p = byte_buf () in
    if not has_data then begin
      (* dyld_chained_fixups_header *)
      u32 p 0;            (* fixups_version *)
      u32 p 0x20;         (* starts_offset *)
      u32 p 0x30;         (* imports_offset *)
      u32 p 0x30;         (* symbols_offset *)
      u32 p 0;            (* imports_count *)
      u32 p 1;            (* imports_format = DYLD_CHAINED_IMPORT *)
      u32 p 0;            (* symbols_format = uncompressed *)
      u32 p 0;            (* pad to starts_offset (0x20) *)
      (* dyld_chained_starts_in_image at 0x20 *)
      u32 p 3;            (* seg_count (pagezero, text, linkedit) *)
      u32 p 0; u32 p 0; u32 p 0;   (* seg_info_offset[3] = none *)
      u32 p 0; u32 p 0   (* trailing pad -> 56 bytes total *)
    end else begin
      (* build the symbol string pool (leading NUL, then each name\0) and record
         each external's name offset within it *)
      let pool = byte_buf () in
      u8 pool 0;
      let name_off = Hashtbl.create 8 in
      List.iter
        (fun name ->
          Hashtbl.replace name_off name (Buffer.length pool);
          String.iter (fun c -> u8 pool (Char.code c)) name;
          u8 pool 0)
        externals;
      let imports_offset = 0x50 in
      let symbols_offset = imports_offset + (nimp * 4) in
      (* dyld_chained_fixups_header *)
      u32 p 0;                       (* fixups_version *)
      u32 p 0x20;                    (* starts_offset *)
      u32 p imports_offset;
      u32 p symbols_offset;
      u32 p nimp;                    (* imports_count *)
      u32 p 1;                       (* imports_format = DYLD_CHAINED_IMPORT *)
      u32 p 0;                       (* symbols_format = uncompressed *)
      u32 p 0;                       (* pad -> 0x20 *)
      (* dyld_chained_starts_in_image at 0x20 (seg_count = 4; __DATA_CONST is
         segment index 2, its starts_in_segment sits 0x18 bytes further on) *)
      u32 p 4;                       (* seg_count *)
      u32 p 0; u32 p 0; u32 p 0x18; u32 p 0;   (* seg_info_offset[4] *)
      u32 p 0;                       (* pad 0x34 -> 0x38 *)
      (* dyld_chained_starts_in_segment at 0x38 *)
      u32 p 24;                      (* size *)
      u16 p vmpage;                  (* page_size = 0x4000 *)
      u16 p 6;                       (* pointer_format = DYLD_CHAINED_PTR_64_OFFSET *)
      u64 p (dataconst_vmaddr - text_seg_vmaddr);  (* segment_offset *)
      u32 p 0;                       (* max_valid_pointer *)
      u16 p 1;                       (* page_count *)
      u16 p 0;                       (* page_start[0] = 0 (chain begins at got[0]) *)
      (* imports table at 0x50: dyld_chained_import bitfield
         lib_ordinal:8 | weak_import:1 | name_offset:23 *)
      List.iter
        (fun name ->
          let noff = Hashtbl.find name_off name in
          u32 p (1 lor (0 lsl 8) lor (noff lsl 9)))  (* lib_ordinal = 1 (libSystem) *)
        externals;
      (* symbol string pool *)
      Buffer.add_buffer p pool;
      while Buffer.length p land 7 <> 0 do u8 p 0 done
    end;
    Buffer.contents p
  in

  (* ---- __LINKEDIT layout ---- *)
  let linkedit_fileoff =
    if has_data then dataconst_fileoff + dataconst_filesize else text_seg_filesize
  in
  let linkedit_vmaddr =
    if has_data then dataconst_vmaddr + dataconst_vmsize
    else text_seg_vmaddr + text_seg_filesize
  in
  let cf_off = linkedit_fileoff in
  let cf_size = String.length chained_payload in
  let exp_off = cf_off + cf_size in
  let exp_size = 0 in
  let symoff = exp_off + exp_size in
  let symsize = nsyms * 16 in
  let stroff = symoff + symsize in
  let sig_start = align_up (stroff + strsize) 16 in

  (* ---- ad-hoc code-signature sizing ---- *)
  let ident_z = ident ^ "\000" in
  let identlen = String.length ident_z in
  let code_limit = sig_start in
  let cs_pagesize = 4096 in
  let ncodeslots = (code_limit + cs_pagesize - 1) / cs_pagesize in
  let cd_hashoffset = 88 + identlen in
  let cd_len = cd_hashoffset + (ncodeslots * 32) in
  let super_len = 12 + 8 + cd_len in
  let sig_size = super_len in
  let linkedit_end = sig_start + sig_size in
  let linkedit_filesize = linkedit_end - linkedit_fileoff in
  let linkedit_vmsize = align_up linkedit_filesize vmpage in

  (* entry point: file offset of the entry function *)
  let main_off =
    match Hashtbl.find_opt dsym entry with
    | Some o -> o
    | None -> failwith ("write_executable: entry symbol " ^ entry ^ " not found")
  in
  let entryoff = text_off + main_off in

  let pad_to b target = while Buffer.length b < target do u8 b 0 done in

  let b = byte_buf () in

  (* ---- mach_header_64 ---- *)
  u32 b mh_magic_64;
  u32 b cpu_type_arm64;
  u32 b cpu_subtype_arm64_all;
  u32 b 0x2;                 (* MH_EXECUTE *)
  u32 b ncmds;
  u32 b sizeofcmds;
  u32 b 0x00200085;          (* NOUNDEFS|DYLDLINK|TWOLEVEL|PIE *)
  u32 b 0;

  (* ---- LC_SEGMENT_64 __PAGEZERO ---- *)
  u32 b lc_segment_64; u32 b cs_pagezero;
  fixed b 16 "__PAGEZERO";
  u64 b 0; u64 b 0x100000000; u64 b 0; u64 b 0;
  u32 b 0; u32 b 0; u32 b 0; u32 b 0;

  (* ---- LC_SEGMENT_64 __TEXT ---- *)
  u32 b lc_segment_64; u32 b cs_textseg;
  fixed b 16 "__TEXT";
  u64 b text_seg_vmaddr; u64 b text_seg_filesize;
  u64 b 0; u64 b text_seg_filesize;
  u32 b 0x5; u32 b 0x5; u32 b 2; u32 b 0;
  (* section __text *)
  fixed b 16 "__text"; fixed b 16 "__TEXT";
  u64 b text_vmaddr; u64 b text_size; u32 b text_off; u32 b 2;
  u32 b 0; u32 b 0; u32 b s_text_flags; u32 b 0; u32 b 0; u32 b 0;
  (* section __cstring *)
  fixed b 16 "__cstring"; fixed b 16 "__TEXT";
  u64 b cstring_vmaddr; u64 b cstring_size; u32 b cstring_off; u32 b 0;
  u32 b 0; u32 b 0; u32 b s_cstring_flags; u32 b 0; u32 b 0; u32 b 0;

  (* ---- LC_SEGMENT_64 __DATA_CONST (only when there are imports) ---- *)
  if has_data then begin
    u32 b lc_segment_64; u32 b cs_dataconst;
    fixed b 16 "__DATA_CONST";
    u64 b dataconst_vmaddr; u64 b dataconst_vmsize;
    u64 b dataconst_fileoff; u64 b dataconst_filesize;
    u32 b 0x3; u32 b 0x3; u32 b 1; u32 b 0x10;  (* rw / rw / 1 sect / SG_READ_ONLY *)
    (* section __got (non-lazy symbol pointers, dyld-bound via chained fixups) *)
    fixed b 16 "__got"; fixed b 16 "__DATA_CONST";
    u64 b dataconst_vmaddr; u64 b got_size; u32 b dataconst_fileoff; u32 b 3;
    u32 b 0; u32 b 0; u32 b 0x00000006; u32 b 0; u32 b 0; u32 b 0
  end;

  (* ---- LC_SEGMENT_64 __LINKEDIT ---- *)
  u32 b lc_segment_64; u32 b cs_linkedit;
  fixed b 16 "__LINKEDIT";
  u64 b linkedit_vmaddr; u64 b linkedit_vmsize;
  u64 b linkedit_fileoff; u64 b linkedit_filesize;
  u32 b 0x1; u32 b 0x1; u32 b 0; u32 b 0;

  (* ---- LC_DYLD_CHAINED_FIXUPS ---- *)
  u32 b lc_dyld_chained_fixups; u32 b cs_chained;
  u32 b cf_off; u32 b cf_size;

  (* ---- LC_DYLD_EXPORTS_TRIE (empty) ---- *)
  u32 b lc_dyld_exports_trie; u32 b cs_exports;
  u32 b exp_off; u32 b exp_size;

  (* ---- LC_SYMTAB ---- *)
  u32 b lc_symtab2; u32 b cs_symtab;
  u32 b symoff; u32 b nsyms; u32 b stroff; u32 b strsize;

  (* ---- LC_DYSYMTAB ---- *)
  u32 b lc_dysymtab; u32 b cs_dysymtab;
  u32 b 0; u32 b 0;            (* ilocalsym / nlocalsym *)
  u32 b 0; u32 b nsyms;        (* iextdefsym / nextdefsym *)
  u32 b nsyms; u32 b 0;        (* iundefsym / nundefsym *)
  u32 b 0; u32 b 0; u32 b 0; u32 b 0; u32 b 0; u32 b 0;
  u32 b 0; u32 b 0; u32 b 0; u32 b 0; u32 b 0; u32 b 0;

  (* ---- LC_LOAD_DYLINKER ---- *)
  u32 b lc_load_dylinker; u32 b cs_dylinker; u32 b 12;
  let dyld = "/usr/lib/dyld" in
  String.iter (fun c -> u8 b (Char.code c)) dyld;
  for _ = String.length dyld to (cs_dylinker - 12) - 1 do u8 b 0 done;

  (* ---- LC_UUID ---- *)
  u32 b lc_uuid; u32 b cs_uuid;
  let uuid = Digest.string (ident ^ ":" ^ string_of_int text_size) in
  String.iter (fun c -> u8 b (Char.code c)) uuid;

  (* ---- LC_BUILD_VERSION ---- *)
  u32 b lc_build_version; u32 b cs_buildver;
  u32 b 1; u32 b 0x000B0000; u32 b 0x000B0000; u32 b 0;

  (* ---- LC_MAIN ---- *)
  u32 b lc_main; u32 b cs_main; u64 b entryoff; u64 b 0;

  (* ---- LC_LOAD_DYLIB (libSystem) ---- *)
  u32 b lc_load_dylib; u32 b cs_dylib; u32 b 24;
  u32 b 2;                    (* timestamp *)
  u32 b 0x054C0000;           (* current version 1356.0.0 *)
  u32 b 0x00010000;           (* compat version 1.0.0 *)
  let libsys = "/usr/lib/libSystem.B.dylib" in
  String.iter (fun c -> u8 b (Char.code c)) libsys;
  for _ = String.length libsys to (cs_dylib - 24) - 1 do u8 b 0 done;

  (* ---- LC_CODE_SIGNATURE ---- *)
  u32 b lc_code_signature; u32 b cs_codesig;
  u32 b sig_start; u32 b sig_size;

  (* ---- pad to __text, then section data (user code + stubs + cstring) ---- *)
  pad_to b text_off;
  Array.iter (fun w -> u32 b w) words;
  String.iter (fun c -> u8 b (Char.code c)) cstring;

  (* ---- __DATA_CONST / __got: one chained-fixup bind pointer per import.
     Each 8-byte slot is a dyld_chained_ptr_64_bind: bind=bit63, next(2 = the
     4-byte stride to the following slot) at bits 51-62, ordinal (import index)
     in the low bits. dyld overwrites each with the real symbol address. *)
  if has_data then begin
    pad_to b dataconst_fileoff;
    for i = 0 to nimp - 1 do
      let next = if i < nimp - 1 then 2 else 0 in
      u32 b i;                                  (* low32: ordinal | addend<<24 *)
      u32 b (0x80000000 lor (next lsl 19))      (* high32: bind<<31 | next<<19 *)
    done
  end;

  (* ---- pad to __LINKEDIT ---- *)
  pad_to b linkedit_fileoff;

  (* ---- chained fixups payload (precomputed above) ---- *)
  Buffer.add_string b chained_payload;

  (* ---- symbol table ---- *)
  List.iter
    (fun (name, off) ->
      u32 b (Hashtbl.find str_off name);
      u8 b (n_sect lor n_ext);   (* 0x0F: N_SECT|N_EXT *)
      u8 b 1;                    (* n_sect = 1 (__text) *)
      u16 b 0;                   (* n_desc *)
      u64 b (text_vmaddr + off)) (* n_value = runtime vmaddr *)
    defined_syms;

  (* ---- string table ---- *)
  Buffer.add_buffer b strtab;

  (* ---- pad to signature start (= codeLimit) ---- *)
  pad_to b sig_start;

  (* Everything up to code_limit is now in [b]; hash it in 4KB pages. *)
  let file_so_far = Buffer.contents b in
  assert (String.length file_so_far = code_limit);
  let hashes = Buffer.create (ncodeslots * 32) in
  for p = 0 to ncodeslots - 1 do
    let start = p * cs_pagesize in
    let len = min cs_pagesize (code_limit - start) in
    Buffer.add_string hashes (Sha256.digest (String.sub file_so_far start len))
  done;

  (* ---- CodeDirectory (big-endian) ---- *)
  let cd = byte_buf () in
  be32 cd 0xfade0c02;         (* magic CSMAGIC_CODEDIRECTORY *)
  be32 cd cd_len;             (* length *)
  be32 cd 0x00020400;         (* version *)
  be32 cd 0x00000002;         (* flags = adhoc *)
  be32 cd cd_hashoffset;      (* hashOffset *)
  be32 cd 88;                 (* identOffset *)
  be32 cd 0;                  (* nSpecialSlots *)
  be32 cd ncodeslots;         (* nCodeSlots *)
  be32 cd code_limit;         (* codeLimit *)
  u8 cd 32;                   (* hashSize *)
  u8 cd 2;                    (* hashType = SHA-256 *)
  u8 cd 0;                    (* platform *)
  u8 cd 12;                   (* pageSize = 2^12 *)
  be32 cd 0;                  (* spare2 *)
  be32 cd 0;                  (* scatterOffset *)
  be32 cd 0;                  (* teamOffset *)
  be32 cd 0;                  (* spare3 *)
  be64 cd 0;                  (* codeLimit64 *)
  be64 cd 0;                  (* execSegBase *)
  be64 cd text_seg_filesize;  (* execSegLimit *)
  be64 cd 1;                  (* execSegFlags = CS_EXECSEG_MAIN_BINARY *)
  String.iter (fun c -> u8 cd (Char.code c)) ident_z;   (* identifier *)
  Buffer.add_buffer cd hashes;
  let cd_bytes = Buffer.contents cd in
  assert (String.length cd_bytes = cd_len);

  (* ---- SuperBlob (big-endian) ---- *)
  be32 b 0xfade0cc0;          (* magic CSMAGIC_EMBEDDED_SIGNATURE *)
  be32 b super_len;           (* length *)
  be32 b 1;                   (* count *)
  be32 b 0;                   (* blob index: type CSSLOT_CODEDIRECTORY *)
  be32 b 20;                  (* blob index: offset *)
  Buffer.add_string b cd_bytes;

  let oc = open_out_bin path in
  Fun.protect ~finally:(fun () -> close_out oc) (fun () ->
      Buffer.output_buffer oc b);
  (* make it executable *)
  (try Unix.chmod path 0o755 with _ -> ())
