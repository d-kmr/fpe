(*---------------------------------*)
(* Csyntax                         *)
(* usage: funcp -f input.sc        *)
(*---------------------------------*)
open Tools;;

(*
module Parser = Simplc_parser;;
module Lexer = Simplc_lexer;;
 *)
module Cprogram = Csyntax.Program;;
module O = FpOption.Option;;
module FPstate = Fpsyntax.State;;
module FPsh = Fpsyntax.StoreHeap;;
module Kmodule = Csyntax.Module;;

(* read from file *)
let inputstr_stdin () =
let x = ref "" in
try
while true do
x := !x ^ (input_line stdin) ^ "\n"
done ;
"" (* dummy *)
with End_of_file -> !x ;;

(* Options *)
let _projectdir = ref "";;
let _funname = ref "main";;
let f_help () = print_endline "help";;
let setDirectory dirname = _projectdir := dirname
let setStartFunc funname = FpOption._startfunc := funname

let msgUsage = "USAGE: fp -d <projectdir> [-debug] [-f <funcname>]\n";;

let speclist = [
    ("-d", Arg.String setDirectory, "project directory");
    ("-debug", Arg.Unit O.setDebug, "Debugging mode");
    ("-f",Arg.String setStartFunc, "Set Start function")
];;

module V = Map.Make(Bytes);;

let pprint_fmodule (fmodule : VcpAllC.t) =
  let (_,fullpath,globalL,structureL,_,_) = fmodule in
  print_endline fullpath;
  List.iter VcpTranslate.Global.pprint globalL;
  V.iter (fun k v -> VcpTranslate.Structure.pprint v) structureL 
;;

let _fmoduleL = ref []
;;
let start curdir =
  if Sys.is_directory curdir then
    begin
      let fpcL = VcpAllC.get_all_C_files curdir in (* (filename,path,cabs)-list *)
      let fmoduleL =
        List.map
          (fun fpc ->
            let rr = VcpAllC.rearrange_a_file fpc in
            let tr = VcpAllC.transform_a_file rr in
            let fmod = VcpAllC.translate_a_file tr in
            fmod
          )
          fpcL
      in
      List.iter pprint_fmodule fmoduleL;
      _fmoduleL := fmoduleL;
      O.sayIfDebug "Modules are loaded"
    end
;;

let theMain () =
  Arg.parse speclist print_endline msgUsage;
  if !_projectdir = "" then print_endline msgUsage
  else
  if Sys.is_directory !_projectdir
  then
    begin
      start !_projectdir; (* parseOneFile *)
      O.doIfDebug print_endline "---";
      let ret = ConvFtoK.fp_toplevel !_fmoduleL !FpOption._startfunc in
      FPstate.println ret
    end
  else
    failwith ""
;;

theMain ();
