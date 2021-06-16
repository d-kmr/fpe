module GI = Fp3.GlobalInfo;;
module V = Map.Make(Bytes);;
open Ftools;;

let theMain () =
  let argc = Array.length Sys.argv in
  if argc <> 2 then
    begin
      print_endline "USAGE: read-fpaFuntable <funtable-file>";
      exit 1
    end
  else
    let file = Sys.argv.(1) in
    let funtable : GI.funTable = read_file file in
    GI.println_funtable funtable
;;

theMain ();
