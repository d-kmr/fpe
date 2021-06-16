module MyFp = Fp3
module MyFpsyntax = Fpsyntax3            
module FPval = MyFpsyntax.Val
module FPsh = MyFpsyntax.StoreHeap
module FPstate = MyFpsyntax.State

open Ftools
module V = Map.Make(Bytes)
         
let theMain () =
  let argc = Array.length Sys.argv in
  if argc <> 2 then
    begin
      print_endline "USAGE: read-fpaSH <initStoreHeap-file>";
      exit 1
    end
  else
    let source = Sys.argv.(1) in
    let ((s,h) : FPsh.t) = read_file source in
    FPsh.println2_s s;
    print_endline "";
    FPsh.println2_h h
;;

theMain ();
