(*---------------------------------*)
(* Manual Input                    *)
(* usage: manualinput -f input.sli *)
(*---------------------------------*)
open Tools;;
open Slsyntax;;
open Manualinput;;
open ConvFtoK;;

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
let _fname = ref "";;
let f_help () = print_endline "help";;
let set_filename fname = _fname := fname

let msgUsage = "USAGE: manualinput -f <filename>.in\n";;

let speclist = [
    ("-f", Arg.String set_filename, "Input file");
];;


let () =
  let display_message () = print_endline msgUsage in
  Arg.parse speclist print_endline msgUsage;
  if !_fname = "" then display_message () else
    let file =  Manualinput.parse (my_read_file !_fname) in
    MIfile.println file
;;
