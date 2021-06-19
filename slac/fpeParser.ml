open Ftools

let theMain () =
  let argc = Array.length Sys.argv in
  if argc < 3 then
    begin
      prerr_endline ("Error: Not enough argument");
      exit 1
    end
  else
    begin
      let source_file = Sys.argv.(1) in
      let dest_file = Sys.argv.(2) in
      let filename = Sys.argv.(3) in
      let cabs_file = VcpAllC.parse_a_file_to_C (source_file, filename) in
      let out = open_out dest_file in
      Marshal.to_channel out cabs_file [];
      close_out out
    end
;;

theMain ();
