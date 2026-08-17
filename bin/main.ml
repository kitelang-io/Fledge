(* kitec — the Kite bootstrap compiler (stage 0), written in OCaml. *)

let version = "0.0.1"

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let usage () =
  prerr_string
    "kitec — the Kite compiler (stage 0)\n\n\
     usage:\n\
    \  kitec version            print the compiler version\n\
    \  kitec lex <file.kite>    tokenize a source file and print the tokens\n\
    \  kitec parse <file.kite>  parse a source file and print the AST\n\
    \  kitec check <file.kite>  parse + name resolution + type check (M2)\n\
    \  kitec asm <file.kite>    emit AArch64 assembly for the codegen subset\n\
    \  kitec run <file.kite>    self-link a native binary (no ld/clang) and run it (exit code)\n\
    \  kitec obj <file.kite>    emit a Mach-O .o directly (own encoder + writer)\n\
    \  kitec exe <file.kite>    self-link a runnable Mach-O executable (no ld/clang)\n";
  exit 1

let cmd_lex path =
  let src = read_file path in
  match Kite.Lexer.tokenize src with
  | toks ->
    List.iter
      (fun { Kite.Token.tok; line; col } ->
        Printf.printf "%4d:%-3d  %s\n" line col (Kite.Token.to_string tok))
      toks
  | exception Kite.Lexer.Lex_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: lex error: %s\n" path line col msg;
    exit 1

let cmd_parse path =
  let src = read_file path in
  match Kite.Parser.parse_program (Kite.Lexer.tokenize src) with
  | prog -> print_string (Kite.Printer.program_to_string prog)
  | exception Kite.Lexer.Lex_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: lex error: %s\n" path line col msg;
    exit 1
  | exception Kite.Parser.Parse_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: parse error: %s\n" path line col msg;
    exit 1

let cmd_check path =
  let src = read_file path in
  match Kite.Parser.parse_program (Kite.Lexer.tokenize src) with
  | prog ->
    let diags = Kite.Resolve.check prog @ Kite.Typecheck.check prog in
    (match diags with
     | [] -> Printf.printf "%s: ok (name resolution + type check passed)\n" path
     | _ ->
       List.iter (fun m -> Printf.eprintf "%s: error: %s\n" path m) diags;
       Printf.eprintf "%s: %d semantic error(s)\n" path (List.length diags);
       exit 1)
  | exception Kite.Lexer.Lex_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: lex error: %s\n" path line col msg;
    exit 1
  | exception Kite.Parser.Parse_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: parse error: %s\n" path line col msg;
    exit 1

let parse_file path =
  let src = read_file path in
  try Kite.Parser.parse_program (Kite.Lexer.tokenize src)
  with
  | Kite.Lexer.Lex_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: lex error: %s\n" path line col msg; exit 1
  | Kite.Parser.Parse_error (msg, line, col) ->
    Printf.eprintf "%s:%d:%d: parse error: %s\n" path line col msg; exit 1

(* Parse several files and concatenate their top-level declarations into one
   program — the bootstrap "module" model: a multi-file Kite program is just the
   union of every file's decls (names must be globally unique). This is what lets
   the Kite compiler-in-Kite be split across files. *)
let parse_files paths = List.concat_map parse_file paths

let cmd_asm paths =
  let prog = parse_files paths in
  try print_string (Kite.Codegen_arm64.emit_program prog)
  with Kite.Codegen_arm64.Codegen_error m -> Printf.eprintf "codegen error: %s\n" m; exit 1

(* Emit a Mach-O object directly (Fledge's own AArch64 encoder + own Mach-O
   writer) for [path], producing the .o file [ofile]. No external assembler
   (clang/as) is involved — only Fledge's encoder + macho.ml. Returns the word
   count / symbol / reloc stats for reporting. *)
let emit_object prog ofile =
  let open Kite.Codegen_arm64 in
  let instrs =
    try program_instrs prog
    with Codegen_error m -> Printf.eprintf "codegen error: %s\n" m; exit 1
  in
  let words, relocs = assemble instrs in
  let macho_relocs =
    List.map
      (fun r ->
        let ro_kind =
          match r.r_kind with
          | RelocBranch26 -> Kite.Macho.Reloc_branch26
          | RelocPage21 -> Kite.Macho.Reloc_page21
          | RelocPageoff12 -> Kite.Macho.Reloc_pageoff12
        in
        { Kite.Macho.ro_off = r.r_off; ro_sym = r.r_sym; ro_kind })
      relocs
  in
  let defined_syms = function_symbols instrs in
  let cstring, cstring_labels = cstring_section () in
  Kite.Macho.write_object ~path:ofile ~text:words ~cstring ~cstring_labels
    ~defined_syms ~relocs:macho_relocs;
  (Array.length words, List.length defined_syms, List.length macho_relocs)

(* Self-link a fully-linked, directly-runnable Mach-O EXECUTABLE for [path],
   writing it to [exe]. This is Fledge's OWN linker (lib/macho.ml's
   write_executable): it lays out the __PAGEZERO/__TEXT/__DATA_CONST/__LINKEDIT
   segments at their runtime vm addresses, resolves the intra-image pc-relative
   branches + adrp/add to our own __cstring, sets LC_MAIN's entry, and emits the
   dyld chained-fixups binding for external imports (printf). NO ld, NO clang,
   NO as is invoked — only dyld loads the result at runtime. Returns
   (text_words, defined_syms, relocs) for reporting. *)
let emit_executable prog exe =
  let open Kite.Codegen_arm64 in
  let instrs =
    try program_instrs prog
    with Codegen_error m -> Printf.eprintf "codegen error: %s\n" m; exit 1
  in
  let words, relocs = assemble instrs in
  let macho_relocs =
    List.map
      (fun r ->
        let ro_kind =
          match r.r_kind with
          | RelocBranch26 -> Kite.Macho.Reloc_branch26
          | RelocPage21 -> Kite.Macho.Reloc_page21
          | RelocPageoff12 -> Kite.Macho.Reloc_pageoff12
        in
        { Kite.Macho.ro_off = r.r_off; ro_sym = r.r_sym; ro_kind })
      relocs
  in
  let defined_syms = function_symbols instrs in
  let cstring, cstring_labels = cstring_section () in
  (try
     Kite.Macho.write_executable ~path:exe ~text:words ~cstring ~cstring_labels
       ~defined_syms ~relocs:macho_relocs ~entry:"_main"
       ~ident:(Filename.basename exe)
   with Failure m -> Printf.eprintf "self-link error: %s\n" m; exit 1);
  (Array.length words, List.length defined_syms, List.length macho_relocs)

(* The native run pipeline:
     parse -> codegen -> encode -> write Mach-O EXECUTABLE (Fledge) -> execute.
   Fledge self-links the binary itself (own object writer + own executable
   linker); NO external assembler or linker (as/ld/clang) is invoked anywhere —
   only the produced binary is executed, and only dyld touches it at runtime. *)
let cmd_run paths =
  let prog = parse_files paths in
  let base = Filename.remove_extension (List.hd paths) in
  let exe = base ^ ".out" in
  let _ = emit_executable prog exe in
  let code = Sys.command (Filename.quote exe) in
  Printf.printf "%s -> exit code %d\n" (Filename.basename exe) code

(* Emit a Mach-O object directly (own AArch64 encoder + own Mach-O writer). *)
let cmd_obj paths =
  let prog = parse_files paths in
  let base = Filename.remove_extension (List.hd paths) in
  let ofile = base ^ ".o" in
  let nwords, nsyms, nrelocs = emit_object prog ofile in
  Printf.printf "wrote %s (%d text words, %d defined syms, %d relocs)\n"
    ofile nwords nsyms nrelocs

(* Self-link a runnable Mach-O executable directly (Fledge's own AArch64
   encoder + own linker in macho.ml). NO ld, NO clang. Only handles programs
   whose cross-symbol references are intra-image bl calls (and adrp/add to our
   own __cstring); external symbols like _printf are a later increment. *)
let cmd_exe paths =
  let prog = parse_files paths in
  let base = Filename.remove_extension (List.hd paths) in
  let nwords, nsyms, nrelocs = emit_executable prog base in
  Printf.printf "wrote %s (%d text words, %d defined syms, %d relocs, self-linked, code-signed)\n"
    base nwords nsyms nrelocs

(* hidden: self-check the AArch64 machine-code encoder *)
let cmd_enctest path_opt =
  let open Kite.Codegen_arm64 in
  let chk name got want =
    if got <> want then (
      Printf.eprintf "FAIL %s: got 0x%08X want 0x%08X\n" name got want;
      exit 1)
  in
  let enc1 i = fst (encode_instr (Hashtbl.create 1) 0 i) in
  chk "ret" (enc1 Ret) 0xD65F03C0;
  chk "movz x0,#2" (enc1 (Movz (0, 2))) 0xD2800040;
  chk "add x0,x0,x1" (enc1 (Add (0, 0, 1))) 0x8B010000;
  (* encode a real program's instruction stream: word count == real instr count *)
  (match path_opt with
   | Some path ->
     let prog = parse_file path in
     let instrs = program_instrs prog in
     let n_real = List.length (List.filter (function Kite.Codegen_arm64.Label _ | Kite.Codegen_arm64.Raw _ -> false | _ -> true) instrs) in
     let words, relocs = assemble instrs in
     if Array.length words <> n_real then (
       Printf.eprintf "FAIL %s: %d words != %d real instrs\n" path (Array.length words) n_real;
       exit 1);
     Printf.printf "encoded %s: %d words, %d relocs (matches real instr count)\n"
       (Filename.basename path) (Array.length words) (List.length relocs);
     if Sys.getenv_opt "ENC_DUMP" <> None then
       Array.iter (fun w -> Printf.printf "%08x\n" w) words
   | None -> ());
  print_string "PASS\n"

let () =
  match Array.to_list Sys.argv with
  | _ :: "version" :: _ -> Printf.printf "kitec %s\n" version
  | _ :: "enctest" :: path :: _ -> cmd_enctest (Some path)
  | _ :: "enctest" :: _ -> cmd_enctest None
  | _ :: "lex" :: path :: _ -> cmd_lex path
  | _ :: "parse" :: path :: _ -> cmd_parse path
  | _ :: "check" :: path :: _ -> cmd_check path
  | _ :: "asm" :: (_ :: _ as paths) -> cmd_asm paths
  | _ :: "run" :: (_ :: _ as paths) -> cmd_run paths
  | _ :: "obj" :: (_ :: _ as paths) -> cmd_obj paths
  | _ :: "exe" :: (_ :: _ as paths) -> cmd_exe paths
  | _ -> usage ()
