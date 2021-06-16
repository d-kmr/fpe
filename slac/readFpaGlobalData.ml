open Ftools

module MyFp = Fp3
module V = Map.Make(Bytes)

let theMain () =
  let argc = Array.length Sys.argv in
  begin
    if argc < 1 then
      begin
        print_endline "USAGE: read-fpaProfile <profile-file>";
        exit 1
      end
    else
      let source = Sys.argv.(1) in
      let (mod_id,name,kdata) : int * bytes * MyFp.kdata = read_file source in
      print_endline ((string_of_int mod_id) ^ " " ^ name ^ " ");
      MyFp.println_kdata kdata
  end
;;

theMain ();
