open Ftools
open VcpBase
open VcpTranslate
module F = Frontc;;
module EL = VcpElements
module F1 = Map.Make(String)
module V  = Map.Make(Bytes)
module G  = Map.Make(String)
          
type filename = string
type fullpath = string
type funcname = string

type t = filename * fullpath * Global.t list * Structure.t V.t * bool * Formula.t * (bytes V.t)
type lib_t = string * string * Exp.attr list * (Exp.t * Block.t list * Block.t)
type cabs_t = (filename * fullpath * Cabs.definition list)
type simple_t = (bytes * bytes * (Cabs.definition list * bytes list))

            
let tot = ref 0

let missing_f = ref []
let used_f = ref []

let prelude =
  "open VcpBase
open Locs
open Op
open Var
open Exp
open Term
open BExp
open Formula
open VcpTranslate
open Block
open Structure
open Procedure
open Global
open VcpAllC
   
let modules () = "
           
let print (filename, fullpath, defs, structures, _, _) =
  p "(";
  p ("\"" ^ filename ^ "\"");
  p ",";
  p ("\"" ^ fullpath ^ "\"");
  p ",";
  print_list Global.print defs; (* this just shows the filename of a saved function-def *)
  p ",";
  let l_structures = V.fold (fun _ v acc -> v::acc) structures [] in
  print_list Structure.print l_structures; 
  p ")\n"

let pprint (filename, fullpath, defs, structures, _, _, aliases) =
  p ("\"" ^ filename ^ "\""); print_newline ();
  p ("\"" ^ fullpath ^ "\""); print_newline ();
  let l_structures = V.fold (fun _ v acc -> v::acc) structures [] in
  List.iter Structure.print l_structures; 
  print_newline ();
  List.iter Global.pprint defs; (* this unmarshals a saved function-def and shows the definition *)
  print_newline ();
  V.iter (fun k v -> p k; p "->"; pn v) aliases;
  print_newline ();
;;
  
let read (filename, fullpath, defs, l_structures) =
  let structures = (fun acc ((sn,_,_) as s) -> V.add sn s acc) |->> (V.empty, l_structures) in
  (filename, fullpath, defs, structures, false, Formula.empty)
  
(*
let is_main (g : Global.t) : bool =
  match g with
    Global.PROC ((proc_name, _, _), _, _, _,  _) -> (* true (* (** dec 19 *) *) *) (Var.to_str proc_name) = "main" 
  | _ -> false
  ;;
 *)

let rec get_all_procs modules funcs = function
    Global.PROC ((fn, _, f), _, _, _, _) ->
    get_procs modules funcs f
  | _ -> []

and get_procs (modules: t list) funcs = function
    Block.PROCCALL (proc_name, _, _, y, _) when Bytes.length (Term.toStr proc_name) > 1 && Bytes.sub (Term.toStr proc_name) 0 1 <> "@" ->
    begin
      (*      List.iter (fun (m, fu) -> prerr_string fu;prerr_string "("; prerr_string m;  prerr_string ")->") funcs; *)
      (* prerr_endline proc_name; *)
      if proc_name |<- (snd |>>| funcs) then
        begin
          (* prerr_endline " REC found"; *)
          get_procs modules funcs y
        end
      else
        let rec find_f (* (prevs: t list) *) = function
            [] -> (* prevs, *) []
          | (_, fpath, gs, _, _, _, _)::xs ->
            let ss = (fun s ->
                match s with
                  Global.PROC ((p_n, _, _), _, _, _, _) when Exp.toStr p_n = Term.toStr proc_name ->
                  [(fpath, s)]
                | _ ->
                  []
              ) |>>| gs in
            let ss' = List.concat ss in
            if ss' = [] then
              find_f (* (prevs @ [(z1, path, gs, z2, z3, z4)]) *) xs
            else
              (* prevs @ [(z1, path, gs', z2, z3, z4)] @ xs, *) ss'
        in
        let fs = find_f (* [] *) modules in
        match fs with
          (m, f)::_ ->
          used_f.contents <- !used_f @ [proc_name];
          let _ = get_all_procs modules (funcs @ [(m, proc_name)]) f in
          get_procs modules funcs y
        | _ ->
          (** Function not found *)
          if !Options.to_be_report_printed then
            begin
              prerr_string "Not found ";
              prerr_endline (Term.toStr proc_name);
            end;
          missing_f.contents <- !missing_f @ [proc_name];
          []
    end
  | Block.SKIP -> []
  | Block.PROCCALL (_, _, _, y, _)
  | Block.LABEL (_, _, y, _)
  | Block.ASSIGN (_, _, y, _)
  | Block.ASSERT (_, y, _) ->
     get_procs modules funcs y
  | Block.IF (a, b, c, y, l) ->
     get_procs modules funcs b @ get_procs modules funcs c @ get_procs modules funcs y
  | Block.BLOCK (b, y, _)
  | Block.WHILE (_, _, b, _, y, _) ->
     get_procs modules funcs b @ get_procs modules funcs y
  | Block.CONS (_, _, y, _)
  | Block.MUTATION (_, _, _, y, _)
  | Block.LOOKUP (_, _, _, y, _)
  | Block.DISPOSE (_, y, _)
  | Block.DECL (_, _, _, y, _)
  | Block.MAPS (_, _, y, _) ->
     get_procs modules funcs y
  | Block.PARALLEL (b, c, y, l) ->
     get_procs modules funcs b @ get_procs modules funcs c @ get_procs modules funcs y
  | Block.MALLOC (a, tl, y, l) ->
     get_procs modules funcs y
  | Block.SARRAY (a, b, tl, y, l) ->
     get_procs modules funcs y
  | Block.RETURN (a, y, _) ->
     get_procs modules funcs y
  | Block.BREAK (y, _) ->
     get_procs modules funcs y
  | Block.CONTINUE (y, _) ->
     get_procs modules funcs y
  | Block.FAIL -> []
;;

let parse_a_file_to_C (fullname, fname) : cabs_t =
  p_s "DOT" ".";
  tot.contents <- !tot + 1;
  (* prerr_string "Parsing "; prerr_string fullname; prerr_string " "; prerr_endline fname; *)
  let cabs = snd (F.parse_to_cabs fullname) in
  pn_s "DONE" ("Parsed " ^ fullname);
  (fname, fullname, cabs);;

let get_all_C_files curdir =
  let rec aux (curdir, dirname) =
    (** Read all the files of current directory *)
    let filesdirs = (fun x -> (curdir ^ "/" ^ x, x)) |>>| (Array.to_list (Sys.readdir curdir)) in
    pn_s "DONE" "List of Files Loaded";
    (** Partition among directory and files *)
    let (dirs, files) = List.partition (fun (x, _) -> Sys.is_directory x) filesdirs in
    (** Filter the *.c files *)
    let files = (fun (_, x) ->
        let len = Bytes.length x in
        let c = Bytes.get x (len-1) in
        let d = Bytes.get x (len-2) in
        c = 'c' && d = '.'
      ) |>- files in
    (** Get vpl of all the sources in current directory *)
    let defs = (parse_a_file_to_C |>>| files) in
    pn_s "DONE" "Parsing and Translation are Finished";
    (** Get vpl of all the sources in sub-directories *)
    let rdefs = List.flatten (aux |>>| dirs) in
    defs @ rdefs
  in
  aux (curdir, curdir)
;;

let transform_a_file (fname, fullname, (cabs, st_names)) =
  let (_, cabs') = Ctransform.transform_file2 (fname, cabs) in
  (fname, fullname, (cabs', st_names))
;;

let rearrange_a_file (fname, fullname, cabs) =
  let (cabs', st_names) = Program.rearrange cabs in
  let res : simple_t =(fname, fullname, (cabs', st_names)) in
  res


let translate_a_file (fname, fullname, (cabs, st_names)) fpdata : t =
  
  let simpleC = Program.translate (cabs, st_names) fpdata in
  (** Get the newly processed structures *)
  let structures = !Block.structures in
  (** Reset the structures of Block *)
  
  
  Block.structures := V.empty;
  let aliases = !Block.s_aliases in
  (** Filter out unsupported globals *)
  let simpleC' = (fun x -> match x with Global.NA -> false | _ -> true ) |>- simpleC in
  pn_s "TR_DONE" ("Translated " ^ fullname);

  
  (fname, fullname, simpleC', structures, false, Formula.empty, aliases)
;;

let split xs n =
  let rec slice i temp acc = function
      [] -> temp::acc
    | x::xs ->
       if i = 1 then
         slice n [] ((x::temp)::acc) xs
       else
         slice (i-1) (x::temp) acc xs
  in 
  slice n [] [] xs


let get_non_amp_funcs programs' f : string list =
  let rec aux = function
    | Block.SKIP ->
       []
    | Block.ASSIGN (_x, _, pr, _) ->
         aux pr
    | Block.IF (_, p1, p2, pr, _) ->
       aux p1 @@ aux p2 @@  aux pr
    | Block.WHILE (_, _, block, _, pr, _) ->
       aux block @@ aux pr
    | Block.CONS (_, _, pr, _) ->
       aux pr
    | Block.MUTATION (_, _, _, pr, _) ->
       aux pr
    | Block.LOOKUP (_x, _, _, pr, _) ->
         aux pr
    | Block.DISPOSE (_, pr, _) ->
       aux pr
    | Block.PROCCALL (a, args, _, pr, _) when Bytes.length (Term.toStr a) > 0 && Bytes.sub (Term.toStr a) 0 1 <> "@" ->
              let is_amp = List.exists (fun a ->
                        match a with Term.EXP (Exp.ADDR _) -> true | _ -> false) args in
       if is_amp then
         aux pr
       else
         Term.toStr  a::aux pr
    | Block.PROCCALL (a, args, _, d, _) ->
       aux d
    | Block.MALLOC (_x, _, pr, _) ->
       aux pr
    | Block.SARRAY (_, _, _, d, _) ->
       aux d
    | Block.BLOCK (e, d, _) -> aux e @@ aux d
    | Block.DECL (_, _, _, d, _) -> aux d
    | Block.RETURN (_, d, _) -> aux d
    | Block.BREAK (d, _) -> aux d
    | Block.CONTINUE (d, _) -> aux d
    | Block.LABEL (_, _, d, _) -> aux d
    | Block.FAIL -> []
    | Block.ASSERT _ -> raise (StError "Assert")
    | Block.PARALLEL _ -> raise (StError "Parallel")
    | Block.MAPS _ -> raise (StError "Maps")
  in
  let (module_name, module_path, attr, (function_name, params, body)) =
    try
      F1.find f programs'
    with
      _ ->
      pn ("Missing Function (C): " ^ f);
      raise Error
  in
  let gs = aux body in
  gs
;;
  
let rec get_funcnames_from_initdata = function
    Block.INIT_E -> []
  | Block.INIT_S t ->
     if Term.with_head t then
         let v = Term.head "get_dependency_0_fp" t in
         if Exp.is_func v then
           [Exp.toStr v]
         else
           []
       else
         []
  | Block.INIT_M idata ->
     List.concat (get_funcnames_from_initdata |>>| idata)
;;
module B = Block

let blacklisted : bytes list ref= ref [];;

let already : bytes list ref = ref [];;

let prev = ref [];;

let e_count = ref 0;;

let is_void v =
  let attr = Exp.get_func_ret v in
  List.for_all (function Exp.SIMPLE _ -> false
                      | Exp.PTR -> false
                      | Exp.STRUCT _ -> false
                      | Exp.ARRAY _ -> false
                      | _ -> true) attr
  


let rec exec_func old_funcs programs func_name =
  let olds : string list = old_funcs @ [func_name] in

  let rec exec_body = function
    | B.SKIP -> true
    | B.ASSIGN (v,t,p1,_) ->
       if Exp.is_funcptr v || Exp.is_global v || Exp.is_param v then
         let b1 = exec_body p1 in
         b1 && false
       else
         if Term.with_head t then
           let h = Term.head "5" t in
           if Exp.is_funcptr h || Exp.is_global h || Exp.is_param h then
             let b1 = exec_body p1 in
             b1 && false
           else
             exec_body p1
         else
           exec_body p1
  | B.IF (_,p1,p2,p3,_) ->
     let b1 = exec_body p1 in
     let b2 = exec_body p2 in
     let b3 = exec_body p3 in
     b1 && b2 && b3
  | B.WHILE (_,_,p1,_,p2,_) ->
     let b1 = exec_body p1 in
     let b2 = exec_body p2 in
     
     b1 && b2

  | B.PROCCALL (proc,_,_,p1,_) ->
     let pv = Term.head "4" proc in
     let ps = Term.toStr proc in
     
     
     if Exp.is_funcptr pv then
       (
         pn ("Function Pointer: " ^ ps ^ " in " ^ func_name);
         let b2 = exec_body p1 in
         b2 && false
       )
     else
       (
         if not (F1.mem ps programs) then
           (
             pn ("Unknown function call: " ^ ps ^ " in " ^ func_name);
             exec_body p1
           )
         else
           (
             if ps |<- olds then
               (
                 pn ("Recursion call: " ^ ps ^ " in " ^ func_name);
                 exec_body p1
               )
             else
               (
                 
                 if Exp.is_func pv then
                   (
                     if ps = "ERR_put_error" then
                       ( e_count := !e_count + 1;
                         exec_body p1
                       )
                     else
                       (
                         let b1 = exec_func olds programs ps in
                         
                         let b2 = exec_body p1 in
                         b1 && b2
                       )
                   )
                 else
                   (
                     let ((file_name : string), (full_path : string), attr, (function_name, params, body)) = F1.find ps programs in
                     pw ("XXXXX " ^ ps); Exp.print pv; pn (" in " ^ full_path);
                     exec_body p1
                   )
               )
           )
       )
  | B.MALLOC (_,_,p1,_) ->
     exec_body p1
  | B.MUTATION (t1,_,t2,p1,_) ->
     if Term.with_head t1 then
       let h = Term.head "3" t1 in
       if Exp.is_funcptr h  || Exp.is_global h || Exp.is_param h then
         let b1 = exec_body p1 in
         b1 && false
       else
         if Term.with_head t2 then
           let h2 = Term.head "2" t2 in
           if Exp.is_funcptr h2  || Exp.is_global h2 || Exp.is_param h2 then
             let b1 = exec_body p1 in
             b1 && false
           else
             exec_body p1
         else
           exec_body p1
     else
       if Term.with_head t2 then
           let h2 = Term.head "2" t2 in
           if Exp.is_funcptr h2  || Exp.is_global h2 || Exp.is_param h2 then
             let b1 = exec_body p1 in
             b1 && false
           else
             exec_body p1
         else
           exec_body p1
  | B.LOOKUP (v,t2,_,p1,_) ->
     if Exp.is_funcptr v || Exp.is_global v || Exp.is_param v then
         let b1 = exec_body p1 in
         b1 && false
     else
       if Term.with_head t2 then
         let h = Term.head "1" t2 in
         if Exp.is_funcptr h || Exp.is_global h || Exp.is_param h then
           let b1 = exec_body p1 in
           b1 && false
         else
           exec_body p1
       else
         exec_body p1
  | B.DISPOSE (_,p1,_) ->
     exec_body p1
  | B.BLOCK (p1,p2,_) ->
     let b1 = exec_body p1 in
     let b2 = exec_body p2 in
     b1 && b2
  | B.DECL (_,_,_,p1,_) ->
     exec_body p1
  | B.RETURN (_,p1,_) ->
     exec_body p1
  | B.LABEL (_,_,p1,_) ->
     exec_body p1
  | _ -> true
  in
  pn ("Exploring " ^ func_name);

  (* if not (old_funcs = !prev) then
    (iterS pw "-> " olds; pn ".\n"); *)

  prev := olds;
  
  if F1.mem func_name programs then
    let ((file_name : string), (full_path : string), attr, (function_name, params, body)) = F1.find func_name programs in
    let b = exec_body body in
    if b then
      ( pn ("Unnecessary: " ^ func_name);
        true )
    else
      ( pn ("Necessary: " ^ func_name);
        false )
  else
    true


  
let blacklist = ref [];;
let count = ref 0;;
let fpptr = ref 0;;

let fp_map = ref G.empty;;

let fp_store : ((bytes * bytes), bytes list) Hashtbl.t = Hashtbl.create 100;;
let fp_heap : ((bytes * bytes), bytes list) Hashtbl.t = Hashtbl.create 100;;

let queue = ref [];;
let headQ = ref 0;; 

let add_to_Q x =
  if x |<- !queue then
    ()
  else(
    pn (x ^ " is added");
    pi (List.length !queue);
    queue := !queue @ [x]
  );;

let print_table tbl =
  Hashtbl.iter (fun (fname, v) fs ->
    p fname; p " . "; p v; p " -> "; iterS p "," fs; pn "") tbl;;

(**
   Assumption:
   1. Function pointer call does not have function pointer parameter
   2. Function pointer call chain to parent call chain recursion is not supported
*)
let add_to_store f v t =
  (** v is required to be a function pointer *)
  let s_t =
    let h = Term.head "add_to_store" t in
    match h with
      Exp.VAR ("$ret",_) ->
       if Hashtbl.mem fp_store ("*", "$ret") then
         Hashtbl.find fp_store ("*", "$ret")
       else
         []
    | _ ->
       let hs = Exp.toStr h in
       if Exp.is_funcptr h then(
         let g = f in
         let f = if Exp.is_global h then "*" else f in
         
         if Hashtbl.mem fp_store (f, hs) then
           Hashtbl.find fp_store (f, hs)
         else(
           pn "*********";
           print_table fp_store;
           pn "*********";
           pn f;
           pn g;
           Exp.pprint v;
           p "=";
           Term.pprint t;
           pn " ..";
           (* if hs = "string-list_c#_6858" then
          raise Error;                      *)
           raise (StError "Unexpected Store")
         )
       )
       else if Exp.is_func h then(
         let s = Exp.toStr h in
         add_to_Q s;
         [s]
       )
       else
         []
  in
  
  let s, f =
    match v with
    | Exp.VAR ("$ret",_) ->
       "$ret", "*"
    | _ ->
       Exp.toStr v,
       if Exp.is_global v then "*" else f
  in
  if Hashtbl.mem fp_store (f, s) then
    let fs = Hashtbl.find fp_store (f, s) in
    Hashtbl.replace fp_store (f, s) (s_t @@ fs)
  else(
    Hashtbl.add fp_store (f,s) s_t
  )
;;

let add_to_store_param f v prev t =
  (** v is required to be a function pointer *)
  let s_t =
    let h =
      match t with
      | Term.EXP (Exp.ADDR h) -> h
      | _ -> Term.head "add_to_store" t
    in
    if Exp.is_funcptr h then
      let hs = Exp.toStr h in
      let f = if Exp.is_global h then "*" else prev in
      if Hashtbl.mem fp_store (f, hs) then
        Hashtbl.find fp_store (f, hs)
      else(
        if hs = "string-list_c#_6858" then
          raise Error;
        pn f;
        Exp.pprint v;
        p "=";
        Term.pprint t;
        pn "";
        raise (StError "Unexpected Store")
      )
    else if Exp.is_func h then(
      let s = Exp.toStr h in
      add_to_Q s;
      [s]
    )
    else
      []
  in
  let s = Exp.toStr v in

  let f = if Exp.is_global v then "*" else f in
  if Hashtbl.mem fp_store (f, s) then
    let fs = Hashtbl.find fp_store (f, s) in
    Hashtbl.replace fp_store (f, s) (s_t @@ fs)
  else
    Hashtbl.add fp_store (f,s) s_t
;;


let add_to_heap f ptr fld t =
  (** 
      MUTATION
      t is required to be a function pointer or function *)
  let s_t =
    let h = Term.head "add_to_store" t in
    if Exp.is_funcptr h then
      let hs = Exp.toStr h in
      let f = if Exp.is_global h then "*" else f in
      if Hashtbl.mem fp_store (f, hs) then
        Hashtbl.find fp_store (f, hs)
      else(
        pn f;
        Term.pprint ptr; p "->"; p fld;
        p "=";
        Term.pprint t;
        pn "";
        raise (StError "Unexpected Store")
      )
    else if Exp.is_func h then(
      let s = Exp.toStr h in
      add_to_Q s;
      [s]
    )
    else
      []
  in
  let vptr = Term.head "" ptr in
  if Exp.is_struct vptr then
    begin
      let s = Exp.get_struct_name vptr in

      if Hashtbl.mem fp_heap (s, fld) then
        let fs = Hashtbl.find fp_heap (s, fld) in
        Hashtbl.replace fp_heap (s, fld) (s_t @@ fs)
      else
        Hashtbl.add fp_heap (s, fld) s_t
    end
;;

let from_heap f v ptr fld =
  (** 
      LOOKUP
      v is required to be a function pointer *)
  let s_t =
    let vptr = Term.head "" ptr in
    if Exp.is_struct vptr then
    begin
      let s = Exp.get_struct_name vptr in
      if Hashtbl.mem fp_heap (s, fld) then
        let fs = Hashtbl.find fp_heap (s, fld) in
        fs
      else
        []
    end
    else
      []
  in

  let s = Exp.toStr v in
  let f = if Exp.is_global v then "*" else f in
  if Hashtbl.mem fp_store (f, s) then
    let fs = Hashtbl.find fp_store (f, s) in
    Hashtbl.replace fp_store (f, s) (s_t @@ fs)
  else
    Hashtbl.add fp_store (f,s) s_t
;;


let get_var_from_param = function
  | Block.ASSIGN (var, _, _, _)
    | Block.CONS (Exp.VAR _ as var, _, _, _) -> var
  | Block.MALLOC (var, _, _, _) -> var
  | Block.MUTATION (obj, fieldname, to_assign, pr, l) -> Term.toExp obj
  | Block.LOOKUP (var, obj, fieldname, pr, l) -> var
  | Block.SARRAY (var,b,c,d,l) -> var
  | Block.DECL (var, _, _, _, _) -> var
  | e -> Exp.VAR ("GLOBAL", [])
;;
  
let rec walk_tree old_funcs (programs : EL.programs_t) ((prev,args) : bytes * Term.t list) func_name =
  pn (func_name ^ " is called");
  let res =
    if EL.is_a_function programs func_name  then
      begin
        (* pn ("Exploring " ^ func_name); *)
        (* ((file_name : string), (full_path : string), attr, (function_name, params, body)) *)
        
           let (c_filepath, (proc, params, body)) = EL.get_function_details programs func_name in
          begin
            if (List.length args = List.length params) then
              begin
                let pa = List.combine params args in
                List.iter (fun (param,arg) ->
                    let prm = get_var_from_param param in
                    if Exp.is_funcptr prm then
                      add_to_store_param func_name prm prev arg
                    else
                      ()
                  ) pa;
              end;
            try
              
              let b = walk_body func_name old_funcs programs body in
              
        (* pn (func_name ^ " in " ^ full_path ^ " is done"); *)
              b
            with
              e ->
              pn "ERROR OCCURED @";
              pn c_filepath;
              raise e
          end
       
      end
    else
      begin
        pn ("Why " ^ func_name ^ " is not in programs?");
        true
      end
  in
  res

and walk_body fname old_funcs (programs : EL.programs_t) pp =
  let rec walk_body pp =
    match pp with
    | B.SKIP -> true
    | B.ASSIGN (v,(Term.EXP (Exp.VAR ("$ret",_)) as t),p1,lc) ->
       if Hashtbl.mem fp_store ("*", "$ret") then
         begin
           add_to_store fname v t;
           let b1 = false in
           let b2 = walk_body p1 in
           b1 && b2
         end
       else
         walk_body p1
    | B.ASSIGN (v,t,p1,lc) ->
       let b1 =
         begin
           try
             let h = Term.head "" t in
             if Exp.is_funcptr h then(
               add_to_store fname v t;
               count := !count + 1;
               false
             )
             else if Exp.is_func h then
               (
                 add_to_store fname v t;
                 count := !count + 1;
                 false
               )
             else
               true
           with
             _ ->
              match t with
                Term.EXP (Exp.ADDR (h)) when EL.is_a_function programs (Exp.toStr h) ->
                 add_to_store fname v (Term.EXP h);
                 false
              | _ ->
                 true
         end
       in
       
       let b2 = walk_body p1 in 
       b1 && b2
    | B.IF (_,p1,p2,p3,_) ->
       count := !count + 1;
       let b1 = walk_body p1 in
       let b2 = walk_body p2 in
       let b3 = walk_body p3 in
       b1 && b2 && b3
    | B.WHILE (_,_,p1,_,p2,_) ->
       count := !count + 1;
       let b1 = walk_body p1 in
       let b2 = walk_body p2 in
       b1 && b2
    | B.PROCCALL (proc,args,qq,p1,lc) ->
       
       let s = Term.toStr proc in       
       let pv = Term.toExp proc in
       let ps = Term.toStr proc in
       let fp t =
         try
           let h = Term.head "PROCCALL" t in
           Exp.is_func h || Exp.is_funcptr h
         with
           _ -> false
       in
       let res =
         if Exp.is_funcptr pv then
           begin

             if not (G.mem s !fp_map) then ( 
               p " *";
               Term.pprint proc; pn "";
               fp_map := G.add s 0 !fp_map;
               fpptr := !fpptr + 1;
               
             )else(
               let c = G.find s !fp_map in
               fp_map := G.add s (c+1) (G.remove s  !fp_map)
             );
             true
           end
         else
           begin
             if not (EL.is_a_function programs ps) then
               begin
                 true
               end
             else
               if ps |<- old_funcs then
                 begin
                   true
                 end
               else
                 begin
                   
                   if s |<- !blacklist then
                     true
                   else(
                     count := !count + 1;
                     pn ps;
                     pb (EL.is_a_function programs ps); pn " :: in programs";
                     let b1 = walk_tree (ps::old_funcs) programs (fname, args) ps in
                     if not b1 then
                       pn (ps ^ " is not blacklisted");
                     
                     if b1 && List.for_all (fun a -> not (fp a)) args then(
                       pn (s ^ " is added to blacklist");
                       blacklist := s::!blacklist);
                     b1)
                 end
           end
       in
       let b2 = walk_body p1 in
       res && b2 
    | B.MALLOC (_,_,p1,_) ->
       count := !count + 1;
       walk_body p1
    | B.MUTATION (t1,fld,t2,p1,lc) ->
       let b1 =
       begin
         try
           let v = Term.head "mutation" t2 in
           if Exp.is_funcptr v then
             ( 
               count := !count + 1;
               add_to_heap fname t1 fld t2;
               false
             )
           else if Exp.is_func v then
           (
             count := !count + 1;
             
             add_to_heap fname t1 fld t2;
             false
           )
           else
             true
         with
           _ ->
           match t2 with
             Term.EXP (Exp.ADDR (h)) when EL.is_a_function programs (Exp.toStr h)  ->
              pause "MUTATION";
              add_to_heap fname t1 fld (Term.EXP h);
              false
           | _ ->
              true
       end
       in
       let b2 = walk_body p1 in
       b1 && b2
    | B.LOOKUP (v,t2,fld,p1,lc) ->
       let b1 =
         if Exp.is_funcptr v then
           (
             count := !count + 1;
             from_heap fname v t2 fld;
             false
           )
         else if Exp.is_func v then
           (
             count := !count + 1;
             from_heap fname v t2 fld;
             false
           )
         else
           true
       in
       let b2 = walk_body p1 in
       b1 && b2
    | B.DISPOSE (_,p1,_) ->
       walk_body p1
    | B.BLOCK (p1,p2,_) ->
       let b1 = walk_body p1 in
       let b2 = walk_body p2 in
       b1 && b2
    | B.DECL (v,_,init,p1,_) ->
       count := !count + 1;
       let for_init t =
         begin
           try
             let h = Term.head "" t in
             if Exp.is_funcptr h then(
               add_to_store fname v t;
               count := !count + 1;
               
               false
             )
             else if Exp.is_func h then
               (
                 add_to_store fname v t;
                 count := !count + 1;
                 
                 false
               )
             else
               true
           with
             _ -> true
         end
       in
       let rec init_case init =
         begin
           match init with
             Block.INIT_E -> true
           | Block.INIT_S t -> for_init t
           | Block.INIT_M ts -> List.for_all (fun t -> init_case t) ts
         end
       in
       let b1 = init_case init in
       let b2 = walk_body p1 in
       b1 && b2
    | B.RETURN (t,p1,_) ->
       count := !count + 1;
       let b =
         begin
           try
             let h = Term.head "" t in
             if Exp.is_funcptr h then(
               add_to_store fname (Exp.VAR ("$ret",[])) t;
               count := !count + 1;
               
               false
             )
             else if Exp.is_func h then
               (
                 add_to_store fname (Exp.VAR ("$ret",[])) t;
                 count := !count + 1;
                 
                 false
               )
             else
               true
           with
             _ -> true
         end
       in
       b && walk_body p1
    | B.LABEL (_,_,p1,_) ->
       walk_body p1
    | _ -> true
  in

  walk_body pp
;;

let rec walk_Q (programs : EL.programs_t) =
  
  if !headQ = List.length !queue then
    ()
  else
    let x = List.nth !queue !headQ  in
    try
      pn ("top(Q): " ^ x);
      let _ = walk_tree [] programs ("",[]) x in
      pause "Next...";
      headQ := !headQ + 1;
      walk_Q programs
    with
      e ->
      pn x;
      raise e
;;

(*
40 class

  12 class practical + 10 theory

             16 class practical

                        13 theory
                      *)

