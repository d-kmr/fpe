open Ftools
open VcpBase

module MyFp = Fp3

let writeInit file data =
  let struct_file = open_out file in
  Marshal.to_channel struct_file data [];
  close_out struct_file;;
      
   
let theInit () =
  let argc = Array.length Sys.argv in
  if argc > 1 then
    begin
      let tempdir = Sys.argv.(1) in

      if not (Sys.is_directory tempdir) then
        begin
          prerr_endline ("Temporary directory " ^ tempdir ^ " does not exist");
          exit (1)
        end;
      if not (Sys.is_directory $$ Shared.init_dir tempdir) then
        begin
          prerr_endline ("Temporary directory " ^ tempdir ^ "/fold must be exist");
          exit (1)
        end;

      pn ("writing init files to " ^ tempdir ^ "/fold");
      let struct_data : VcpTranslate.Structure.t list = [] in
      writeInit (Shared.struct_file tempdir) struct_data;
      
      (*      let init_data : Analyzer.t * FPstate.t * FPretStack.t = Fp2.initialization () in *)
      let init_data : MyFp.GlobalInfo.t * MyFp.FPstate.t = MyFp.initialization () in
      writeInit (Shared.az_file tempdir) init_data;
      
      (* print_gc (Gc.stat ()); *)
      exit(0)
    end
  else
    prerr_endline "Usage: slac-init <dir>"
;;

theInit ();;
  
