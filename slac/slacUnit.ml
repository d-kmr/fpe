open Ftools
   
module F = Frontc
module S = VcpBase.Shared

let checkDirectory dir =
  if not (Sys.is_directory dir) then
    begin
      prerr_endline ("Temporary directory " ^ dir ^ " does not exist");
      exit (1)
    end
;;


         
let theMain () =
  let argc = Array.length Sys.argv in
  if argc <= 3 then
    begin
      prerr_endline "Usage: slac-unit <filename> <dir>"
    end
  else
    begin
      let slacDataDir = Sys.argv.(1) in
      let translatedDir = S.get_translated_dir slacDataDir in
      let fpaDir = S.get_fpa_dir slacDataDir in
      let fpaFundefDir = S.get_fpa_fundef_dir fpaDir in
      let fpaGlobalDataDir = S.get_fpa_global_data_dir fpaDir in
      let fpaProfileDir = S.get_fpa_profile_dir fpaDir in
      checkDirectory slacDataDir;
      checkDirectory translatedDir;
      checkDirectory fpaDir;
      checkDirectory fpaFundefDir;
      checkDirectory fpaGlobalDataDir;
      checkDirectory fpaProfileDir;
      
      let srcfile = Sys.argv.(2) in
      let module_id_s = Sys.argv.(3) in
      let module_id = int_of_string module_id_s in

      let ii = if Array.length Sys.argv < 5 || Sys.argv.(4) = "-deb" then
                 4
               else
                 begin
                   VcpBase.Options.fp_json_file := Sys.argv.(4);
                   5
                 end
      in
      let dbg = ref [] in
      let is_tr_only = ref false in
      for i = ii to Array.length Sys.argv - 1 do
        if Sys.argv.(i) = "-t" then
          VcpBase.Options.show_types := true
        else if Sys.argv.(i) = "-tr" then
          is_tr_only := true
        else
          dbg := Sys.argv.(i)::!dbg
      done;
      p_opt := !dbg;
      
      funcdir.contents <- translatedDir ^ "/func";

      let (fname, fullname, cabs) : VcpAllC.cabs_t = read_file srcfile in (* Marshal.from_channel fin in *)
      let flattenpath = flatten_path fullname in            
      (* print_endline ("BEGIN: " ^ flattenpath); *)

      let prefix = S.sub_str fullname translatedDir in
      
      let ssrc = flatten_path prefix in

      let ffile = translatedDir ^ "/" ^ flattenpath in
      let fpaFunDefFile = fpaFundefDir ^ "/" ^ module_id_s in
      let fpaGlobalDataFile = fpaGlobalDataDir ^ "/" ^ module_id_s in

      (* pn ("Prefix: " ^ ssrc); *)
      cfunc.contents <- ssrc;

      (* iterS Cprint.print_def "" cabs; *)

      
      
      (* let cabs' = VcpFpOnC.transform_cabs cabs in *)
      
      let simple_cabs = VcpAllC.rearrange_a_file (fname, fullname, cabs) in
      pn_s "DONES" "Rearrangement is done";
      
      let transformed_cabs = VcpAllC.transform_a_file simple_cabs in
      pn_s "DONES" "Transformation is done";

      let fpdata = VcpFpOnC.get_fpdata () in
      
      let _Fmod : VcpAllC.t = VcpAllC.translate_a_file transformed_cabs fpdata in
      write_file ffile (module_id, _Fmod);
      
(*
      let aux1 = function
        | VcpTranslate.Global.FFILE (file_name, fn) ->
           let g' : VcpTranslate.Global.t = read_file file_name in
           g'
        | x -> x
      in

      let aux2 = function
        | VcpTranslate.Global.PROC ((pname, _, _), _, _, _, _) -> true
        | x -> false
      in
      
      let aux3 = function
        | VcpTranslate.Global.PROC ((pname, _, x), _, _, _, _) ->
           VcpBase.Exp.pprint pname; pn "";
           x
        | x -> raise Error
      in
      
      let aux (a,b,( d : VcpTranslate.Global.t list),c,e,f) =
        let d' = aux1 |>>| d in
        let d'' = aux2 |>- d' in
        let d''' = aux3 |>>| d'' in
        d'''
      in

      pn "toT started";
      
      let _ffff : VcpPrecond2.t list = VcpPrecond2.toT |>>| (aux _Fmod) in

      iterS (fun f -> p "-") "," _ffff;

      pn "toT finished";
 *)
      
      pn_s "DONES" "Translation is done";
      if not !is_tr_only then
        begin
          let (_Kdata,_KfundefL) = ConvFtoK.fp_preAnalyze_a_module _Fmod module_id in

          write_file fpaGlobalDataFile (module_id,srcfile,_Kdata);
          write_file fpaFunDefFile (module_id,srcfile,_KfundefL);
          
          (* let fout = open_out (translatedDir ^ "/" ^ flattenpath) in
      Marshal.to_channel fout (arg_i, kfile, _Fmod, _Kdata) [];
      close_out fout; *)


          (* let kmod = open_out kfile in
      Marshal.to_channel kmod (arg_i, _Kmod) [];
      close_out kmod; *)

          (* print_endline ("END: " ^ flattenpath); print_newline (); *)
          (* print_gc (Gc.stat ()); *)
          exit(0)
        end
       
    end
;;

theMain ();
