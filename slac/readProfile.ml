open Ftools

module MyFp = Fp3
module Profile = MyFp.FunProfile
module V = Map.Make(Bytes)

let theMain () =
  let argc = Array.length Sys.argv in
    begin
      if argc < 1 then
        begin
          print_endline "Usage: read-profile <path-to-function-profile>";
          exit 1
        end
  else
    let source = Sys.argv.(1) in
    let (prof : Profile.t) = read_file source in
    Profile.println prof
    end
;;

theMain ();
