open Ftools
module V = Map.Make(Bytes)

let theMain () =
  let argc = Array.length Sys.argv in
    begin
      if argc < 1 then
        begin
          prerr_endline ("Error: Not enough argument");
          exit 1
        end
  else
    let source = Sys.argv.(1) in
    let (_, ((_,_,globals,structs,_,_,_) : VcpAllC.t)) = read_file source in
    if Array.length Sys.argv > 2 then
      if Sys.argv.(2) = "-t" then
        VcpBase.Options.show_types := true;
    iterS VcpTranslate.Global.pprint "" globals;
    pn "";
    V.iter (fun k v -> VcpTranslate.Structure.pprint v) structs;
    end
;;

theMain ();
