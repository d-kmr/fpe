(*------------------------------------------------------*)
(*  Validity Checker of Entailments with Array		*)
(*  compile:   $ make_array				*)
(*  usage:     $ sliarray < input > output		*)
(*------------------------------------------------------*)
open Tools;;
open Slsyntax
open Slparser;;
open Entlcheck;;
open Entlcheck.Flags;;

let inputstr_stdin () =
  let x = ref "" in
  try
    while true do
      x := !x ^ (input_line stdin) ^ "\n"
    done ;
    "" (* dummy *)
  with End_of_file -> !x ;;

let parserbody str =
  let module P = SLparser in
  try
    match P.parse P.isPseudoPS str with
    | None -> failwith "Illegal Input\n"
    | Some(ps,rest) -> convPseudoPS ps
  with
    P.ParseError mes -> failwith ("Error: "^mes)
;;

(*----------------Argv options-------------------------*)
let flags = {
  output=0;
  decomp=false;
  opt=true
};;
  
let f_help () = print_endline "help help";;
let set_out () = flags.Flags.output <- 1;;
let set_smtout () = flags.Flags.output <- 2;;
let set_dcmp () = flags.Flags.decomp <- true;;
let set_noopt () = flags.Flags.opt <- false;;

let speclist = [
  ("-out", Arg.Unit set_out, "Output the normally formatted output of the generated formula");
  ("-smtout", Arg.Unit set_smtout, "Output the smt2-formatted output of the generated formula");
  ("-decomp", Arg.Unit set_dcmp, "Check by decomposing disjunction on RHS");
    ("-noopt", Arg.Unit set_noopt, "Check without optimization");
];;

let usagemsg = "sliarray usage:\n $ sliarray < FILE.sli\n";;
let f_anon s = print_endline s;;

let () =
  Arg.parse speclist f_anon usagemsg;
  let str = inputstr_stdin () in
  let ps_m = parserbody str in
  let ps = PS_mes.extract ps_m in
  let deciding = if flags.decomp then decide_ps_decomp else decide_ps in
  if deciding flags (PS.nf ps)
  then
    print_string "Result: Valid\n"
  else
    print_string "Result: Invalid\n"
;;
