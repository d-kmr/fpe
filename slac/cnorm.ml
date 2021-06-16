module F = Frontc

let parse_and_print fname =
  let cabs = F.parse_to_cabs fname in
  Cprint.printFile cabs;; 
  
(***** MAIN *****)  
let theMain () =
  (* let _ = VcpAllC.start (* parseOneFile *) Sys.argv.(1) in *)
  let _ = parse_and_print Sys.argv.(1) in
  exit(1)
;;
                                        (* Define a wrapper for main to 
                                         * intercept the exit *)


theMain (); 

