(*------------------------------*)
(* C transformer                *)
(* usage: ctransform file.c     *)
(*------------------------------*)
open Tools;;
open Cprint;;
open Ctransform;;
open Ftools
module F = Frontc
module Opt = CtransformOptions;;

let msgUsage = "USAGE: ctransform <dirname>\n";;

let () =
  Opt.debugFlag := true;
  let argc = Array.length Sys.argv in  
  let display_message () = print_endline msgUsage in
  if argc < 2 || 4 < argc then (display_message(); exit 0) else ();

  let srcdir = Sys.argv.(1) in

  let dbg = ref [] in
  if argc == 3 && Sys.argv.(2) = "-debug"
  then dbg := Sys.argv.(2)::!dbg
  else ();
  p_opt := !dbg;

  let cabs_files : VcpAllC.cabs_t list = VcpAllC.get_all_C_files srcdir in
  
  for i = 0 to List.length cabs_files - 1 do
    let cabsfile : VcpAllC.cabs_t = List.nth cabs_files i in
    let simple_cabsfile : VcpAllC.simple_t = VcpAllC.rearrange_a_file cabsfile in
    let _ =  VcpAllC.transform_a_file simple_cabsfile in
    ()
  done;
;;
