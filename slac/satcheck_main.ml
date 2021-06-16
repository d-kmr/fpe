(*------------------------------*)
(* Satcheck                     *)
(* usage: satcheck -f input.sat *)
(*------------------------------*)
open Tools;;
open Slsyntax;;

module Parser = Slsyntax_parser_sh;;
module Lexer = Slsyntax_lexer_sh;;
module SatResult = Smttoz3.SatcheckResult;;

(* read from file *)
let inputstr_stdin () =
let x = ref "" in
try
while true do
x := !x ^ (input_line stdin) ^ "\n"
done ;
"" (* dummy *)
with End_of_file -> !x ;;

let inputstr_file filename =
  let x = ref "" in
  let ic = open_in filename in
  try
	while true do
	  x := !x ^ (input_line ic) ^ "\n"
	done ;
	"" (* dummy *)
  with End_of_file -> close_in ic;!x
;;

(* Options *)
let _fname = ref "";;
let _rawflag = ref false;;
let _modelflag = ref false;;
let _ucflag = ref false;;
let _bnflag = ref false;;
let f_help () = print_endline "help";;
let set_filename fname = _fname := fname;;
let set_raw () = _rawflag := true;;
let set_model () = _modelflag := true;;
let set_unsatcore () = _ucflag := true;;
let set_bignum () = _bnflag := true;;
let set_foption opt = Ftools.p_opt := opt :: !Ftools.p_opt;;

let msgUsage =
"USAGE: satcheck [-0|-u|-t|-h|-d <TAG>] -f <filename>.sat";;

let speclist = [
    ("-f", Arg.String set_filename, "Input file");
    ("-d", Arg.String set_foption,
     "Set Foption
    Z3: show the translation result (smt2 input for Z3)
    UC: produce & show unsatcore when an input is unsat
    MD: produce & show a model when an input is sat");
    ("-b", Arg.Unit set_bignum, "Bignumber support ON (values of hat variables are assumed to be bignumbers)");
    ("-0", Arg.Unit set_raw, "Use raw z3 (Only checking the pure-part with Z3 ignoring the spat-part)");
];;

(* parser *)
let parse str = 
  Parser.main Lexer.token 
    (Lexing.from_string str)
;;

let () =
  let _p = ref P.True in
  let _ss = ref [] in
  let _startMesHeader = ref "" in
  let _startMesUnsatcore = ref "" in
  let _startMesRaw = ref "" in
  let _pMes = ref "" in
  let _ssMes = ref "" in  
  let display_message () = print_endline msgUsage in
  Arg.parse speclist print_endline msgUsage;
  let check_fname () = if !_fname = "" then (display_message (); exit(0)) else () in
  let do_parse () = 
    let (p,ss) = parse (inputstr_file !_fname) in
    _p := p;
    _ss := ss;
    _pMes := P.to_string !_p;
    _ssMes := SS.to_string !_ss;
  in
  let init_raw () =
    if !_rawflag then
      begin
        _startMesRaw := "RAW-MODE ";
        _ss := [];
        _ssMes := "Ignored"
      end
    else ()
  in
  (* body *)
  check_fname ();
  do_parse ();
  init_raw ();
  print_endline @@ "Satchecker " ^ !_startMesRaw ^ "\n";
  print_endline @@ "Satcheck Input:";
  print_endline @@ "Pure: " ^ !_pMes;
  print_endline @@ "Spat: " ^ !_ssMes;
  print_newline ();
  let sh = (!_p,!_ss) in
  Ftools.pf_s "MD" set_model ();
  Ftools.pf_s "UC" set_unsatcore ();
  match !_rawflag with
  | true ->
     begin     
       match Smttoz3.checkSatExp ~modelflag:!_modelflag ~ucflag:!_ucflag (Sltosmt.mkExp_p !_p) with         
       | SatResult.Model model ->
          print_endline "Result: SAT";
          if !_modelflag then
            begin
              print_newline ();
              print_endline "[Found Model]";
              List.iter (fun (s,bn) -> print_endline ("(" ^ s ^ "," ^ (Bignum.to_string bn) ^ ")")) model
            end
       | SatResult.UnsatCore uc ->
          print_endline "Result: UNSAT";
          if !_ucflag then
            begin
              print_newline ();
              print_endline "[Unsatcore]";
              List.iter (fun e -> print_endline (Z3.Expr.to_string e)) uc
            end
       | SatResult.Unknown ->
          print_endline "Result: UNKNOWN";
     end
  | false ->
     begin
       match Satcheck.satcheck_bn ~modelflag:!_modelflag ~ucflag:!_ucflag ~bnflag:!_bnflag sh with
       | SatResult.Model model ->
          print_endline "Result: SAT";
          if !_modelflag then
            begin
              print_newline ();
              print_endline "[Found Model]";
              List.iter (fun (s,bn) -> print_endline ("(" ^ s ^ "," ^ (Bignum.to_string bn) ^ ")")) model
            end
       | SatResult.UnsatCore uc ->
          print_endline "Result: UNSAT";
          if !_ucflag then
            begin
              print_newline ();
              print_endline "[Unsatcore]";
              List.iter (fun e -> print_endline (Z3.Expr.to_string e)) uc
            end
       | SatResult.Unknown ->
          print_endline "Result: UNKNOWN";
     end
;;

