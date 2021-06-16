open Ftools

let theMain () =
  let argc = Array.length Sys.argv in
    begin
      if argc < 1 then
        begin
          prerr_endline ("Error: Not enough argument");
          exit 1
        end
  else
    let source_dir = Sys.argv.(1) in
    if Sys.is_directory source_dir then
      begin
        let cabs_files = VcpAllC.get_all_C_files source_dir in
        List.iter (fun ((fname,path,_) as c) ->
            let out = open_out (make_path (source_dir ^ "/SlacData/Parsed/") path (flatten_path fname)) in
            Marshal.to_channel out c [];
            close_out out
          ) cabs_files;
        (* pn "Parsing is done"; *)

        
        exit(0)
      end
    else
      prerr_endline ("Illegal argument: " ^ source_dir ^ " is not a directory.\nCorrect command: slac DIRECTORY FUNCTION")
    end
;;

theMain ();
