open Ftools
   
module F = Frontc
module S = VcpBase.Shared
         
let theMain () =
  let argc = Array.length Sys.argv in
  if argc <= 1 then
    begin
      prerr_endline "Usage: slac-unit <filename> <dir>"
    end
  else
    begin
      let cabsFile = Sys.argv.(1) in
      VcpBase.Options.fp_json_file := Sys.argv.(2);
      let (fname, fullname, cabs) : VcpAllC.cabs_t = read_file cabsFile in (* Marshal.from_channel fin in *)

      (* p_opt := ["STRUCTURE"]; *)
      let prefix = S.sub_str fname "" in      
      let ssrc = flatten_path prefix in
      cfunc.contents <- ssrc;
      let simple_cabs = VcpAllC.rearrange_a_file (fname, fullname, cabs) in
      let fpdata = VcpFpOnC.get_fpdata () in
      let _Fmod : VcpAllC.t = VcpAllC.translate_a_file simple_cabs fpdata in
      ()
    end
;;

theMain ();
