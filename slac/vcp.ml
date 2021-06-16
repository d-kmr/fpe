(* open VcpVerify P*)


let print_help _ =
  Ftools.pn "
SLAC (Separation Logic based Analyzer for C)
";
  Ftools.pn "Usage:
slac.native DIRECTORY/SlacData [FUNCTION] [-a] [-u UNKNOWN] [-d PARAMETER VALUE]\n
DIRECTORY
   The path of the source code root directory.
FUNCTION
   The name of the function to be analyzed as the toplevel function.

Options:
--------
 -a
   Outputs the preconditions of all functions.
 -u UNKNOWN
   UNKNOWN is a plain text file containing list of functions (one
      function each line) that should not be analyzed due to having recursion
      or other unsupported feature. In absense of this option, all
      available dependencies are analyzed prior to analysis of the
      top-level function.
 -d PARAMETER VALUE
   A user can specify a value for a 'int' typed formal parameter.
   PARAMETER
      A formal parameter (of type 'int') name of the function name
   VALUE
      An interger that is to be provided as the actual parameter (i.e. argument) of PARAMETER
             \n";;


let rec handle_options = function
    [] -> ()
  | x::xs ->
     if x = "-a" then
      begin
         Ftools.p_opt := ("PRECOND"::(!Ftools.p_opt));
        handle_options xs
      end
     else if x = "-u" then
      begin
        let filename = List.hd xs in
        let xs = List.tl xs in
        let ch = open_in filename in
        let rec rd_ln lns =
          try
            let l = input_line ch in
            rd_ln (l::lns)
          with
            _ -> close_in ch; List.rev lns
        in
        let lines = rd_ln [] in
        VcpBase.Options.unknowns.contents <- lines;
        handle_options xs
      end
     else if x = "-d" then
       begin
         let pname = List.hd xs in
         let xs = List.tl xs in
         let arg = List.hd xs in
         let xs = List.tl xs in
         VcpBase.Options.param.contents <- Some (pname, int_of_string arg);
         handle_options xs
       end
     else if x = "-i" then
       begin
         VcpBase.Options.interactive := true;
         handle_options xs
       end
     else if x = "-I" then
       begin
         VcpBase.Options.interactive_ref := true;
         handle_options xs
       end
     else if x = "-p" then
       begin
         Ftools.is_debug := true;
         handle_options xs
       end
     else if x = "-r" then
       begin
         VcpBase.Options.recompute_specs := true;
         handle_options xs
       end
     else if x = "-e" then
       begin
         VcpBase.Options.catch_exception := true;
         handle_options xs
       end
     else if x = "-deb" then
       begin
         Ftools.p_opt := ((List.hd xs)::(!Ftools.p_opt));
         handle_options (List.tl xs)
       end
     else if x = "-debfun" then
       begin
         VcpBase.Options.debfun := (List.hd xs);
         handle_options (List.tl xs)
       end
     else if x = "-dump_to" then
       begin
         VcpBase.Options.dump_to := (List.hd xs);
         handle_options (List.tl xs)
       end
     else if x = "-pre_to" then
       begin
         VcpBase.Options.pre_to := (List.hd xs);
         handle_options (List.tl xs)
       end
     else if x = "-pre_from" then
       begin
         VcpBase.Options.pre_from := (List.hd xs);
         handle_options (List.tl xs)
       end
     else if x = "-read_from" then
       begin
         VcpBase.Options.read_from := (List.hd xs);
         handle_options (List.tl xs)
       end
     else if x = "-t" then
      begin
        VcpBase.Options.show_types.contents <- true;
        handle_options xs
      end
    else if x = "-m" then
      begin
        let y = List.hd xs in
        let xs = List.tl xs in
        VcpBase.Options.manuals.contents <- y;
        handle_options xs
      end
    else if x = "-c" then
      begin
        VcpBase.Options.to_be_code_printed.contents <- true;
        handle_options xs
      end
    else
      begin
        Ftools.pn ("Unknown option " ^ x);
        print_help ();
      end
;;

let cmd_arg_handler () =
  let argc = Array.length Sys.argv in
  begin
    if argc < 2 then
      begin
        prerr_endline ("Error: Not enough argument");
        exit 1
      end
    else
      let project_dir = Sys.argv.(1) in (* <openssl>/SlacData *)
      if Sys.is_directory project_dir then
        begin
          let options =
            if Sys.argv.(2) <> "-i" && Sys.argv.(2) <> "-I" then
              begin
                let func_name = Sys.argv.(2) in
                VcpBase.Options.functions := func_name;
                Array.to_list (Array.sub Sys.argv 3 (argc - 3))
              end
            else
              Array.to_list (Array.sub Sys.argv 2 (argc - 2))
          in
          handle_options options;
          project_dir
        end
      else
        begin
          prerr_endline (
            "Illegal argument: " ^
              project_dir ^
                " is not a directory.\nCorrect command: slac DIRECTORY FUNCTION"
            );
          exit 1
        end
  end

;;

(***** MAIN *****)
let theMain () =
  let project_dir = cmd_arg_handler () in
  VcpLib.start project_dir;
  Ftools.pn "Program finishes"
;;

theMain ();
