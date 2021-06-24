open Ftools
open VcpTranslate
open VcpBase
   
   
module F = Map.Make(String)
module G = Map.Make(String)
module M = Map.Make(Exp)
module P2 = Block
module EL = VcpElements


          
exception ModuleNotFound
exception NotFound of string

type t = string * string * Exp.attr list * (Exp.t * Block.t list * Block.t)
       
(*
type d = (Fp.Analyzer.t * Fp.FPstate.t * Fp.FPstate.t)
 *)

let get_unique_func proc mod_name =
  (* if proc = "main" then
    proc ^ "@" ^ (Bytes.sub mod_name 0 (Bytes.length mod_name - 2))
  else *)
  proc

let stt s = Term.encode (s,[])

let _V s = (s, [])
let _TT v = Term.encode v
let _T e = Term.EXP e
let _C n = Exp.CONST n

let get_manual_funcs manual_specs =
  (fun (a1, b1, bexp1, uformula1, d1) ->
    let (attrs, fname, params') = List.hd a1 in
    fname
  ) |>>| manual_specs

let get_manual_specs global_store programs manual_specs : (Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t) F.t =
  let global_store' =
    M.fold (fun key value gs ->
        if Exp.is_funcptr key then
          M.add key value gs
        else
          let key_bar = Term.EXP (Exp.set_bar key) in
          M.add key key_bar gs) global_store M.empty in

  let get_body fname =
    let body =
      try
        let (module_name, (function_name, params, body)) = EL.get_function_details programs fname  in
        body
      with
        _ -> Block.SKIP
    in
    VcpPrecond2.toT false body
  in

  let make_store b1 =
    (fun s (x,t) -> M.add (Exp.VAR (x,[])) t s) |->> (global_store', b1)
  in

  let res =
    (fun mfs (a1, b1, bexp1, uformula1, d1) ->
      let s = make_store b1 in
      let d = [bexp1] in
      let (attrs, fname, params') = List.hd a1 in
      let params = (fun x -> Term.EXP x) |>>| params' in
      let specs' = (fun (r, e1, bexp2, b, a) ->
          let s' = make_store e1 in
          let d' = [bexp2] in
          (r, (s,d,b), (s',d',a))
        ) |>>| d1 in
      let specs : VcpPrecond2.specs = (specs', VcpPrecond2.false_d) in
      let body = get_body fname in
      let fdata : Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t = (attrs, params, specs, body) in
      F.add fname fdata mfs
    ) |->> (F.empty, manual_specs) in

  F.iter (fun fname (attrs, params, (specs, _), _) ->
      pn fname;
      iterS Term.pprint "," params; pn "";
      iterS (fun (r, (s,d,b), (s',d',a)) ->
          Term.pprint r; pw ",";
          iterS BExp.pprint "&" d'; pw ",";
          Formula.upprint a; pw ",";
          Formula.upprint b; pn ""
        ) "\n" specs
    ) res;

  res

module FPtr = struct
  type t = bytes * int

  let compare (fn1, fp1) (fn2, fp2) =
    let r1 = Bytes.compare fn1 fn2 in
    if r1 = 0 then
      let r2 = fp1 - fp2 in
      r2
    else
      r1
end;;

module FP = Map.Make(FPtr)
          
module Func = Map.Make(Bytes)

module FGlobal = Map.Make(Bytes)

let funcp' funpos modules =               

  (* NOTE from Kimura *)
  (* funpos = [((fname1,fp1,pos1),fnameL1);((fname2,fp2,pos2),fnameL2)] *)
  (* s2' is dummy *)
  let s1 = funpos in
  let s2' = [] in
  
  let s2 = (function (_, (Exp.NEGINF, Exp.POSINF)) -> false | _ -> true ) |>- s2' in
  dbg "FPA" "|s1|:" pl (List.length s1);
  dbg "GLO" "|s2|:" pi (List.length s2);

  dbg "FPS" "s1:" (iterS (fun ((a,b,c), l_fns) ->
                       p "("; p a; p ", "; p b; p ", "; pl c; p ")"; p " -> {"; iterS pw "" l_fns; pn "}"
                     ) "\n") s1;
  let m_s1 = (fun m ((a,_,c), l_fns) -> FP.add (a,c) l_fns m) |->> (FP.empty, s1) in
  
  let imp_fns = List.sort_uniq Bytes.compare (((fun ((fn,_,_),_) -> fn) |>>| s1) @ ((fun ((fn,_), _) -> fn) |>>| s2')) in
  
  let m_s2 = (fun m ((fn, gv), intv) ->
      if Func.mem fn m then
        let m1 = Func.find fn m in
        let m1' = (gv, intv):: m1 in
        Func.add fn m1' (Func.remove fn m)
      else
        let m1 = [(gv, intv)] in
        Func.add fn m1 m
    ) |->> (Func.empty, s2) in

  let rec should_be_modified proc_name = function 
    | P2.PROCCALL (proc, ps, pos, pr, l) ->
       let proc_head = Term.head "FP_head" proc in
       if Exp.is_funcptr proc_head then
         begin
           try
             let key = (proc_name, pos) in
             let l_funcs = FP.find key m_s1 in
             if List.length l_funcs = 0 then
               should_be_modified proc_name pr
             else
               true
           with
             Not_found ->
             should_be_modified proc_name pr
         end
       else
         should_be_modified proc_name pr
       
    | P2.SKIP -> false
    | P2.ASSERT (a, p, b) ->
       should_be_modified proc_name p
    | P2.ASSIGN (v, e_term, p, l) ->
       should_be_modified proc_name p
    | P2.IF (b, p1, p2, p, l) ->
       should_be_modified proc_name p1 || should_be_modified proc_name p2 || should_be_modified proc_name p
    | P2.WHILE (b, ptn, p1, a, p, l) ->
       should_be_modified proc_name p1 || should_be_modified proc_name p
    | P2.CONS (e, a, p, l) ->
       should_be_modified proc_name p
    | P2.MUTATION (t1, a, t2, p, l) ->
       should_be_modified proc_name p
    | P2.LOOKUP (v, t1, a, p, l) ->
       should_be_modified proc_name p
    | P2.DISPOSE (t, p, l) ->
       should_be_modified proc_name p
    | P2.MAPS (v1, v2, p, l) ->
       should_be_modified proc_name p
    | P2.PARALLEL (p1, p2, p, l) ->
       should_be_modified proc_name p1 || should_be_modified proc_name p2 || should_be_modified proc_name p
    | P2.SARRAY (v, t, tl, p, l) ->
       should_be_modified proc_name p
    | P2.MALLOC (v, tl, p, l) ->
       should_be_modified proc_name p
    | P2.BLOCK (t, p, l) ->
       should_be_modified proc_name t || should_be_modified proc_name p
    | P2.DECL (a, len, data, p, l) ->
       should_be_modified proc_name p
    | P2.RETURN (t, p, l) ->
       should_be_modified proc_name p
    | P2.BREAK ( p, l) ->
       should_be_modified proc_name p
    | P2.CONTINUE (p, l) ->
       should_be_modified proc_name p
    | P2.LABEL (t, _, p, l) ->
       should_be_modified proc_name p
    | P2.FAIL -> false
  in
  
  let rec subs_fp_in_body proc_name stmt =
    match stmt with
    | P2.PROCCALL (proc, ps, pos, pr, l) ->
       let p2 = subs_fp_in_body proc_name pr in
       let proc_head = Term.head "FP_head" proc in
       if Exp.is_funcptr proc_head then
         begin
           try
             let s_proc = Term.toStr proc in
             let key = (proc_name, pos) in
             let l_funcs = FP.find key m_s1 in
             dbg "FPAs" "ProcName:" p proc_name;
             dbg "FPAs" "Fp:" p s_proc;
             dbg "FPAs" "pos:" pl pos;
             dbg "FPAs" "l_funcs:" (iterS p ",") l_funcs;
             if List.length l_funcs = 0 then
               P2.PROCCALL (proc, ps, pos, p2, l)
             else
               let p0 = P2.FAIL in
               let p1 = (fun else_part func ->
                   let t_func = Term.encode (func, []) in
                   P2.IF(BExp.(proc == t_func),
                         P2.PROCCALL (t_func, ps, pos, P2.SKIP, l),
                         else_part,
                         P2.SKIP,
                         l)
                 ) |->> (p0, List.tl l_funcs) in
               let func = (List.hd l_funcs, []) in
               let t_func = Term.encode func in
               P2.IF (BExp.(proc == t_func),
                      P2.PROCCALL (t_func, ps, pos, P2.SKIP, l),
                      p1,
                      p2,
                      l)
           with
             Not_found ->
             P2.PROCCALL (proc, ps, pos, p2, l)
         end
       else
         let p2 = subs_fp_in_body proc_name pr in
         P2.PROCCALL (proc, ps, pos, p2, l)
    | P2.SKIP -> P2.SKIP
    | P2.ASSERT (a, p, b) ->
       let p2 = subs_fp_in_body proc_name p in
       P2.ASSERT (a, p2, b)
    | P2.ASSIGN (v, e_term, p, l) ->
       P2.ASSIGN (v, e_term, subs_fp_in_body proc_name p, l)
    | P2.IF (b, p1, p2, p, l) ->
       P2.IF (b,
              subs_fp_in_body proc_name p1,
              subs_fp_in_body proc_name p2,
              subs_fp_in_body proc_name p, l)
    | P2.WHILE (b, ptn, p1, a, p, l) ->
       P2.WHILE (b, ptn, subs_fp_in_body proc_name p1, a, subs_fp_in_body proc_name p, l)
    | P2.CONS (e, a, p, l) ->
       P2.CONS (e, a, subs_fp_in_body proc_name p, l)
    | P2.MUTATION (t1, a, t2, p, l) ->
       P2.MUTATION (t1, a, t2, subs_fp_in_body proc_name p, l)
    | P2.LOOKUP (v, t1, a, p, l) ->
       P2.LOOKUP (v, t1, a, subs_fp_in_body proc_name p, l)
    | P2.DISPOSE (t, p, l) ->
       P2.DISPOSE (t, subs_fp_in_body proc_name p, l)
    | P2.MAPS (v1, v2, p, l) ->
       P2.MAPS (v1, v2, subs_fp_in_body proc_name p, l)
    | P2.PARALLEL (p1, p2, p, l) ->
       P2.PARALLEL (subs_fp_in_body proc_name p1, subs_fp_in_body proc_name p2, subs_fp_in_body proc_name p, l)
    | P2.SARRAY (v, t, tl, p, l) ->
       P2.SARRAY (v, t, tl, subs_fp_in_body proc_name p, l)
    | P2.MALLOC (v, tl, p, l) ->
       P2.MALLOC (v, tl, subs_fp_in_body proc_name p, l)
    | P2.BLOCK (t, p, l) ->
       P2.BLOCK (subs_fp_in_body proc_name t, subs_fp_in_body proc_name p, l)
    | P2.DECL (a, len, data, p, l) ->
       P2.DECL (a, len, data, subs_fp_in_body proc_name p, l)
    | P2.RETURN (t, p, l) ->
       P2.RETURN (t, subs_fp_in_body proc_name p, l)
    | P2.BREAK ( p, l) ->
       P2.BREAK (subs_fp_in_body proc_name p, l)
    | P2.CONTINUE (p, l) ->
       P2.CONTINUE (subs_fp_in_body proc_name p, l)
    | P2.LABEL (t, el, p, l) ->
       P2.LABEL (t, el, subs_fp_in_body proc_name p, l)
    | P2.FAIL -> P2.FAIL
  in
  
  let subs_fp_in_proc mod_name (ppp, params, body) : Procedure.t =
    let (proc_name, attr) = Exp.var ppp in
    let proc_name' = get_unique_func proc_name mod_name in
    dbg "FPAs" "FP Substituting:" p proc_name;
    let body' =
      if should_be_modified proc_name' body then
        begin
          let body' = subs_fp_in_body proc_name' body in
          pf_s "FPAsource" pn proc_name;
          pf_s "FPAsource" (Block.pprint 0) body;
          pf_s "FPAsource" pn ">>>>>>>>>>>>>>>>>";
          pf_s "FPAsource" (Block.pprint 0) body';
          pf_s "FPAsource" pn "*%#*%#*%#*%#*%#*%#";
          body'
        end
      else
        body
    in
    if Func.mem proc_name m_s2 then
      let gvm' = Func.find proc_name m_s2 in
      let p_fvs = Exp.toStr |>>| Block.fv body' in
      let gvm = (fun (a,_) -> a |<- p_fvs) |>- gvm' in
      dbg "GLO" "Inserting Global condition for " p proc_name;
      dbg "GLO" "s2:" (iterS (fun (b, (c,d)) ->
                           p b; p "->["; Exp.pprint c; p ","; Exp.pprint d; p "]"
                         ) "; ") gvm;

      let _T e = Term.EXP e in
      let _TT v = Term.encode v in
      let build_cond v (l:Exp.t) (u:Exp.t) =
        let t_l : Term.t = _T l in
        let t_u = _T u in
        let t_v = _TT (v, []) in
        match l, u with
          Exp.NEGINF, Exp.POSINF -> None
        | Exp.NEGINF, _ -> Some BExp.(t_v <=. t_u)
        | _, Exp.POSINF -> Some BExp.(t_l <=. t_v)
        | _, _ -> Some BExp.((t_l <=. t_v) &. (t_v <=. t_u))
      in
      let cond = (fun cond (gv, (l,u)) ->
          match build_cond gv l u with
            None -> cond
          | Some b -> BExp.(cond &. b)) |->> (BExp._T, gvm) in
      let body'' =
        if cond = BExp._T then
          body'
        else
          P2.BLOCK (P2.IF (cond, body', P2.FAIL, P2.SKIP, Locs.dummy), P2.SKIP, Locs.dummy) in
      (Exp.VAR (proc_name,attr), params, body'')
    else
      (Exp.VAR (proc_name,attr), params, body')
  in
  
  let rec subs_fp_in_global mod_name = function
      Global.PROC (proc, p, q, r, s) -> Global.PROC (subs_fp_in_proc mod_name proc, p, q, r, s)
    | Global.FFILE (st, fn) ->
       if fn |<- imp_fns then
         begin
           let fin = open_in st in
           let g : Global.t = Marshal.from_channel fin in
           close_in fin;
           subs_fp_in_global mod_name g
         end
       else
         begin
           let g : Global.t = read_file st in
           g
         end
    | x -> x
  in
  
  let subs_fp_in_modules (name, fpath, l_globals, p1, q, r, _) =
    let l_globals' = (subs_fp_in_global name) |>>| l_globals in
    (* if !Options.to_be_code_printed then
      iterS Global.pprint "" l_globals';
     *)
    
    let rr = (name, fpath, l_globals', p1, q, r, V.empty) in
    dbg "FPA" "FPA Done:" p fpath;
    rr
  in

  let modules' = subs_fp_in_modules |>>| modules in

  pn_s "FPA" "**********************************";
  pf_s "FPA" (iterS (fun (_, _, l_globals, _, _, _, _) -> iterS Global.pprint "\n" l_globals) "\n\n") modules';
  
  modules';;


let split_modules modules : (Exp.t * Block.t list * Block.t) list * (Global.t list * bool * Formula.ut * Term.t M.t) F.t =
  let count = ref 1 in
  (fun (fns, acc) (name, fpath, l_globals, _, _, _, _) ->
    dbg "MOD" ((string_of_int !count) ^ "- ") p fpath;
    count.contents <- !count + 1;
    let (global_decls, func_names) = (fun (gd, fn) g ->
        match g with
          Global.PROC (((procname, params, body), _, _, _, _)) -> (gd, fn @ [(procname, params, body)])
        | Global.STRUCT (the_struct, ls) ->
           (* if !Options.to_be_code_printed then begin Global.pprint g end; *)
           (gd, fn)
        | _ ->
           (* if !Options.to_be_code_printed then Global.pprint g; *)
           (gd @ [g], fn)
      ) |->> (([],[]), l_globals) in

    (fns @ func_names, F.add name (global_decls , false, VcpPrecond2.empty, M.empty) acc)
  ) |->> (([], F.empty), modules)


let rec get_function_dependencies ((old_funcs : string list), old_modules) programs (func_name : string) =
  try
    pn_s "SINGLE" ("Checking dependencies for " ^ func_name);
    let ((file_name : string), (full_path : string), attr, (function_name, params, body)) = F.find func_name programs in 
    pn_s "SINGLE" ("Found in " ^ full_path);

    let olds : string list = old_funcs @ [func_name] in
    let called_functions' : string list = fst |>>| VcpDep.get_dependency_0 body in
    
    let called_functions, _ =
      if !Options.unknowns=[] then
        called_functions',[]
      else
        List.partition (fun cf -> not (cf |<- !Options.unknowns)) called_functions' in
    pn_s "SINGLE" ("Called procedures are: ");
    pf_s "SINGLE" (iterS p ",") (called_functions);
    pn_s "SINGLE" "";
    let new_functions : string list = List.filter (fun x -> not (x |<- olds)) called_functions in
    let res : string list * string list =
      (fun acc new_f -> get_function_dependencies acc programs new_f) |->> ((olds, old_modules @@ [file_name]), new_functions) in
    res
  with
    _ ->
    p_s "AUTO" ("int " ^ (func_name) ^ " (");
    (old_funcs, old_modules)
;;

let get_function_dependencies_ref curdir (programs : EL.programs_t) (func_name : string) =

  let rec aux (old_funcs, old_modules, call_graph) programs func_name =
    try
    pn_s "SINGLE" ("Checking dependencies for " ^ func_name);
    let (_, _, ms_filepath, ms_funcpath) = EL.get_function programs func_name in
    let (_, _, body) = EL.read_function ms_funcpath in
    let olds : string list = old_funcs @ [func_name] in
    let called_functions' : string list = fst |>>| VcpDep.get_dependency_0 body in
    let called_functions, _ =
      if !Options.unknowns=[] then
        called_functions',[]
      else
        List.partition (fun cf -> not (cf |<- !Options.unknowns)) called_functions'
    in   
    pn_s "SINGLE" ("Called procedures are: ");
    pf_s "SINGLE" (iterS p ",") (called_functions);
    pn_s "SINGLE" "";
    let new_functions : string list = List.filter (fun x -> not (x |<- olds)) called_functions in
    let call_graph' = F.add func_name called_functions call_graph in
    let res : string list * EL.ms_filepath list * bytes list F.t =
      (fun acc new_f -> aux acc programs new_f) |->> ((olds, old_modules @@ [ms_filepath], call_graph'), new_functions) in
    res
    with
      Not_found -> (old_funcs, old_modules, call_graph)
  in
  aux ([], [], F.empty) programs func_name
;;


let interatcive_process modules programs =
  
  let is_running = ref true in
  while !is_running do
    pn "Enter command: 'f' for function lookup, 'm' for module lookup, 'q' for quit";
    let cmd = read_line () in
    if cmd = "q" then
      is_running := false
    else if cmd = "f" then
      begin
        try
          pn "Enter function name:";
          let fn = read_line () in
          let ((file_name : string), (full_path : string), attr, (function_name, params, body)) = F.find fn programs in
          pn full_path;
          pn "Next action: (p) Print function, (t) Print with types, (d) dependency list result (n) Next";
          let ans = read_line () in
          if ans = "p" then
            Procedure.pprint (function_name, params, body)
          else if ans = "t" then
            begin
              let t = !Options.show_types in
              Options.show_types := true;
              Procedure.pprint (function_name, params, body);
              Options.show_types := t
            end
          else if ans = "d" then
            begin
              pn "Enter list of functions to be ignored (comma separated)";
              let s_ignores = read_line () in
              let l_ignores = split ',' s_ignores in
              let ls, _ = VcpDep.get_dependency_set_of_list ~mods:modules G.empty fn l_ignores in
              pi (List.length ls)
            end
          (* else if ans = "w" then
            begin
              let t1 = Sys.time () in
              List.iter (fun (filename, _, l_globals, _, _, _, _) ->
                  pn filename;
                  List.iter (function Global.STATEMENT s ->
                                       let _ = VcpAllC.walk_body "*" [] programs s in
                                       ()
                                     | _ -> ()) l_globals;
                ) modules;
              Hashtbl.iter (fun (fname, v) fs ->
                  p fname; p " . "; p v; p " -> "; iterS p "," fs; pn ""
                ) VcpAllC.fp_store;
              
              let t2 = Sys.time () in
              pn ("Time (Global): " ^ (string_of_float (t2 -. t1)));

              VcpAllC.queue := [fn];
              let _ = VcpAllC.walk_Q programs in

              let t3 = Sys.time () in
              pn ("Time: " ^ (string_of_float (t3 -. t2)));
              
              pn "Number of statements:";
              pi !VcpAllC.count;
              pn "Number of fp_ptr call:";
              pi !VcpAllC.fpptr;
              pn "STORE:";
              Hashtbl.iter (fun (fname, v) fs ->
                  p fname; p " . "; p v; p " ==> "; iterS p ", " fs; pn ""
                ) VcpAllC.fp_store;
              pn "HEAP:";
              Hashtbl.iter (fun (sname, fld) fs ->
                  p sname; p " -> "; p fld; p " ==> "; iterS p ", " fs; pn ""
                ) VcpAllC.fp_heap
            end *)
          else
            ()
        with
          Not_found ->
          pn "Not found"
      end
    else if cmd = "m" then
      begin
        pn "Enter function name:";
        let fn = read_line () in
        pn "Show types? (y/n)";
        let ans = read_line () in
        if ans = "y" then
          let md = List.find (fun (name, _, l_globals, _, _, _, _) -> name = fn) modules in
          let (_, _, l_globals, _, _, _, _) = md in
          iterS Global.pprint "" l_globals
        ; ()
      end
    else
      ()
  done
;;

let get_programs modules : t F.t =
  let count = ref 1 in
  (fun (acc : t F.t) (name, fpath, l_globals, _, _, _, _) ->
    dbg "MOD" ((string_of_int !count) ^ ". ") p fpath;
    count.contents <- !count + 1;
    (fun (acc : t F.t) g ->
      match g with
      Global.PROC (((proc, params, body), _, _, _, _)) ->
         let fname = Exp.toStr proc in
         let attr = Exp.get_attributes proc in
         let value : t = (name, fpath, attr, (proc, params, body)) in
         F.add fname value acc
       | Global.FFILE (filename, fn) ->
          begin
            let (proc, params, body) = EL.read_function filename in
            let fname = Exp.toStr proc in
            let attr = Exp.get_attributes proc in
            let value : t = (name, fpath, attr, (proc, params, body)) in
            F.add fname value acc
         end 
      | _ -> acc
    ) |->> (acc, l_globals)) |->> (F.empty, modules)
;;

let get_programs_ref ms_filepath acc moduledata : EL.programs_t =
  let (c_filename, c_filepath, l_globals, _, _, _, _) = moduledata in
    (fun (acc : EL.programs_t) g ->
      match g with
      | Global.FFILE (ms_funcpath, fn) ->
         let value = EL.get_function_ref c_filename c_filepath ms_filepath ms_funcpath in
         EL.add_to_programs fn value acc
      | _ -> acc
    ) |->> (acc, l_globals)
;;

(** Returns only relative paths *)
let get_all_modulepaths dirpath =
  let files_arr = Sys.readdir dirpath in
  Array.sort Bytes.compare files_arr;
  let files = Array.to_list files_arr in
  
  let full_path f = (dirpath ^ "/" ^ f) in
  (fun f -> not (Sys.is_directory (full_path f))) |>- files
;;

let build_programs_ref curdir files =
  let f1 acc filepath =
    let (i, moduledata) : (int * VcpAllC.t) = read_file (curdir ^ "/" ^ filepath) in
    let acc = get_programs_ref filepath acc moduledata in
    acc
  in
  let res = f1 |->> (EL.V.empty, files) in
  res
;;

let get_structs_from_vars sofar structs vs =
  let rec get_structs_from_var ?is_rec:(recc=false) sofar structs v =
    if Exp.is_struct v then
      let s_name = Exp.get_struct_name v in
      if V.mem s_name sofar then
        sofar
      else
        try
          let (_, fields_val, _) as s =
            try
              V.find s_name structs
            with
              e ->
              pn "Exception occurs in get_struct_from_vars";
              V.iter (fun s _ -> pw s) structs; pn "";
              Exp.print v; pn "";
              pn (s_name ^ " is not found");
              raise e
          in
          let sofar' = V.add s_name s sofar in
          let fields = fst |>>| fields_val in
          let all = (fun sofar field -> get_structs_from_var ~is_rec:true sofar structs field) |->> (sofar', fields) in
          all
        with
          e ->
          if recc || s_name = "voidp" then
            sofar
          else
            begin
              raise e
            end
    else
      sofar
  in
  (fun sofar v -> get_structs_from_var sofar structs v) |->> (sofar, vs)
;;

let compact_module necessary_funcs l_globals structs : (Global.t list * Structure.t V.t) =

  let gmfvs = G.empty in (** Here we will do complete local analysis *)
  dbg "FILES" "Number of globals:" pl (List.length l_globals);
  
  let (l_globals':Global.t list), (mfvs' : bool G.t), structs' =
    (fun (gcc, mfvs, local_structs) g ->
                      
      match g with
      | Global.PROC ((pname, _, _), _, _, _, _) ->
         raise (StError "Global definitions should not contain PROC")
      | Global.STRUCT _ ->
         (gcc, mfvs, local_structs)
      | Global.STATEMENT b ->
         let v : Exp.t = VcpPrecond2.get_var_from_param "I don't know" b in
         let s_v = fst (Exp.var v) in
                         
         let fvb' = Block.fv b in
         let local_structs' =
           try
             get_structs_from_vars local_structs structs fvb'
           with
             e ->
             pn "Exception occurs in 'compact module'";
             Global.pprint g;
             raise e
         in

         let fvb = Exp.toStr |>>| (Exp.is_func |>- fvb') in
         let vs = fst |>>| (Exp.var |>>| fvb') in
                         
         if Exp.is_funcptr v || List.length fvb > 0 || (G.mem s_v mfvs && not (G.mem s_v gmfvs)) then
           begin
             let mfvs' = (fun m a -> G.add a true m) |->> (mfvs, fvb@@vs) in
             (g::gcc, mfvs', local_structs')
           end
         else
           begin
             (gcc, mfvs, local_structs)
           end
      | Global.FFILE (file_name, fn) ->
         begin      
           if fn |<- necessary_funcs then
             let g' : Global.t = read_file file_name in
             match g' with
             | Global.PROC ((pname, _, _), _, _, _, _) ->
                let e_fvs : Exp.t list = Global.fv [g'] in
                let local_structs' =
                  try
                    get_structs_from_vars local_structs structs e_fvs
                  with
                    e ->
                    pn "Exception occurs in compact module (Global.FFILE (Global.PROC _))";
                    Global.pprint g;
                    pn "-----------";
                    iterS (Exp.pprint) " " e_fvs;
                    pn "---------";
                    raise e
                in
                
                let fvs : string list = Exp.toStr |>>| e_fvs in
                
                let p_n = Exp.toStr pname in
                
                let mfvs' = (fun m a -> G.add a true m) |->> (mfvs, fvs@[Exp.toStr pname]) in
                dbg "FILES" "" p (p_n ^ ": " ^ string_of_int (List.length fvs) );
                (gcc, mfvs', local_structs') (** Funcdef is not included in globals anymore *)
             | _ -> (gcc, mfvs, local_structs)
           else
             (gcc, mfvs, local_structs)
         end
      | _ -> (gcc, mfvs, local_structs)
    ) |->> (([], gmfvs, V.empty), List.rev l_globals)
  in
  
  dbg "FILES" "Number of globals after filter:" pl (List.length l_globals');
  dbg "FILES" "Number of free variables:" pl (G.cardinal mfvs');
  
  l_globals', structs'
;;

let compact_modules curdir necessary_funcs necessary_modules files =
  let res =
    (fun acc ms_filepath ->
      if ms_filepath |<- necessary_modules then
        begin
          let s = curdir ^ "/" ^ ms_filepath in
          let (_, (name, fpath, l_globals, structs, b, c, _)) = read_file s in
          let res = try
              compact_module necessary_funcs l_globals structs
            with
              e ->
              pn "Exception occurs";
              pn name;
              pn ms_filepath;
              raise e
          in
          let ms_filepath' = curdir ^ "/Compacted/" ^ ms_filepath in
          write_file ms_filepath' res;
          F.add ms_filepath ms_filepath' acc
        end
      else
        begin
          acc
        end
    ) |->> (F.empty, files) in
  res
;;


let get_dependency_and_programs_ref curdir =

  (** Relative paths of original simple C translations under Translated dir. *)
  let files : EL.ms_filepath list = get_all_modulepaths curdir in
  let programs : EL.programs_t = build_programs_ref curdir files in
  let top_level_function = !Options.functions in

  let (necessary_funcs, necessary_modules, call_graph) =
    get_function_dependencies_ref curdir programs top_level_function in
  
  dbg "FILES" "Necessary Functions:" (iterS p ",") necessary_funcs;
  dbg "FILES" "Necessary Files:" (iterS p "\n") necessary_modules;
  (** Filter global declarations *)
  let modules_map = compact_modules curdir necessary_funcs necessary_modules files in
  pf_s "SOURCE" (F.iter (fun ms_orig ms_path ->
                     let l_globals, structs = read_file ms_path in 
                     pn ms_orig;
                     pn "#%#%#%#%#%#%#%#%";
                     iterS Global.pprint "\n" l_globals)) modules_map;

  (** function names sorted according to the new dependency *)
  let (sorted_functions, _, _, self_ref) = VcpDep.get_dependencies2 call_graph in
  pn_s "DONES" "Dependencies analysis finished";
  dbg "REC" "self ref:" (iterS p ", ") self_ref;

  (modules_map, programs, sorted_functions, self_ref)
;;


let get_dependency_and_programs modules =
  
  let programs'' : t F.t = get_programs modules in
  
  let modules, programs' =
    if !Options.functions = "" then
      modules, programs''
    else
      begin
        let init_func_calls = (!Options.functions, []) in
        dbg "FILES" "Init Func Calls:" Exp.var_pprint init_func_calls;
        
        let (necessary_funcs, necessary_modules) =
          (fun acc (fn,_) ->
            p_s "FILES" "||"; pn_s "FILES" (fn);
            get_function_dependencies acc programs'' fn
          ) |->> (([],[]), [init_func_calls]) in
        pn_s "FILES" ("All proccalls and files are: ");
        pf_s "FILES" (iterS p ",") necessary_funcs;
        pn_s "FILES" "";
        pf_s "FILES" (iterS p "\n") necessary_modules;
        pn_s "FILES" "";

        pn "Original Modules:"; pi (List.length modules);

        (**
           task: Compact modules and modules data to keep only necesary information. 
         *)

        let get_structs_from_vars sofar structs vs =
          let rec get_structs_from_var ?is_rec:(recc=false) sofar structs v =
            if Exp.is_struct v then
              let s_name = Exp.get_struct_name v in
              if V.mem s_name sofar then
                sofar
              else
                try
                  let (_, fields_val, _) as s =
                    try
                      V.find s_name structs
                    with
                      e ->
                      Exp.print v; pn "";
                      pn (s_name ^ " is not found");
                      raise e
                  in
                  let sofar' = V.add s_name s sofar in
                  let fields = fst |>>| fields_val in
                  let all = (fun sofar field -> get_structs_from_var ~is_rec:true sofar structs field) |->> (sofar', fields) in
                  all
                with
                  e ->
                  if recc then
                    sofar
                  else
                    raise e
            else
              sofar
          in
          (fun sofar v -> get_structs_from_var sofar structs v) |->> (sofar, vs)
        in
        
        let compact_modules modules necessary_funcs necessary_modules =
          
          let modules, _ =
            (fun (acc, (gmfvs : bool G.t)) (name, fpath, l_globals, structs, b, c, _) ->
              
              if name |<- necessary_modules then
                begin
                  
                  dbg "FILESs" "cp" p (fpath ^ " ../" ^ !Options.functions);
                  dbg "FILES" "Path:" p fpath;
                  dbg "FILES" "Number of globals:" pl (List.length l_globals);
                  
                  let (l_globals':Global.t list), (mfvs' : bool G.t), structs' =
                    (fun (gcc, mfvs, local_structs) g ->
                      
                      match g with
                      | Global.PROC ((pname, _, _), _, _, _, _) ->
                         let e_fvs : Exp.t list = Global.fv [g] in
                         let local_structs' =
                           try
                             get_structs_from_vars local_structs structs e_fvs
                           with
                             e ->
                             pn name;
                             Global.pprint g;
                             pn "-----------";
                             raise e
                         in
                         let fvs : string list = Exp.toStr |>>| e_fvs in
                         let p_n = Exp.toStr pname in
                         
                         if p_n |<- necessary_funcs && (!Options.unknowns=[] || not (p_n |<- !Options.unknowns)) then
                           begin
                             dbg "FILES" "" p (p_n ^ ": " ^ string_of_int (List.length fvs) );
                             let mfvs' = (fun m a -> G.add a true m) |->> (mfvs, fvs@[Exp.toStr pname]) in
                             (g::gcc, mfvs', local_structs')
                           end
                         else
                           begin
                             (gcc, mfvs, local_structs)
                           end
                      | Global.STRUCT _ -> (gcc, mfvs, local_structs)
                      | Global.STATEMENT b ->
                         let v : Exp.t = VcpPrecond2.get_var_from_param name b in
                         let s_v = fst (Exp.var v) in
                         
                         let fvb' = Block.fv b in
                         let local_structs' =
                           try
                             get_structs_from_vars local_structs structs fvb'
                           with
                             e ->
                             pn name;
                             Global.pprint g;
                             pn "-----------";
                             raise e
                         in

                         let fvb = Exp.toStr |>>| (Exp.is_func |>- fvb') in
                         let vs = fst |>>| (Exp.var |>>| fvb') in
                         
                         if Exp.is_funcptr v || List.length fvb > 0 || (G.mem s_v mfvs && not (G.mem s_v gmfvs)) then
                           begin
                             let mfvs' = (fun m a -> G.add a true m) |->> (mfvs, fvb@@vs) in
                             (g::gcc, mfvs', local_structs')
                           end
                         else
                           begin
                             (gcc, mfvs, local_structs)
                           end
                      | Global.FFILE (file_name, fn) ->
                         begin
                           
                           if fn |<- necessary_funcs then
                             let g' : Global.t = read_file file_name in
                             match g' with
                             | Global.PROC ((pname, _, _), _, _, _, _) ->
                                let e_fvs : Exp.t list = Global.fv [g'] in
                                let local_structs' =
                                  try
                                    get_structs_from_vars local_structs structs e_fvs
                                  with
                                    e ->
                                    pn name;
                                    Global.pprint g;
                                    pn "-----------";
                                    raise e
                                in
                         
                                let fvs : string list = Exp.toStr |>>| e_fvs in
                                
                                let p_n = Exp.toStr pname in
                                
                                let mfvs' = (fun m a -> G.add a true m) |->> (mfvs, fvs@[Exp.toStr pname]) in
                                dbg "FILES" "" p (p_n ^ ": " ^ string_of_int (List.length fvs) );
                                (g'::gcc, mfvs', local_structs')
                                
                             | _ -> (gcc, mfvs, local_structs)
                           else
                             (gcc, mfvs, local_structs)
                         end
                      | _ -> (gcc, mfvs, local_structs)
                    ) |->> (([], gmfvs, V.empty), List.rev l_globals)
                  in
                  
                  dbg "FILES" "Number of globals after filter:" pl (List.length l_globals');
                  dbg "FILES" "Number of free variables:" pl (G.cardinal mfvs');

                  let modules' : VcpAllC.t list = acc @ [(name, fpath, l_globals', structs', b, c, V.empty)] in
                  (modules', mfvs')
                end
              else
                (acc, gmfvs)
            ) |->> (([], G.empty), modules)
          in
          modules 
        in

        let modules = compact_modules modules necessary_funcs necessary_modules in

        let sum = (fun acc (_, _, _, structs, _, _, _) -> acc + (V.cardinal structs)) |->> (0, modules) in
        pw "Total Number of structs:"; pi sum;
        
        (modules, programs'')
        
      end
  in

  pn "Used Modules:"; pi (List.length modules);
  
  pf_s "SOURCE" (iterS (fun (_, _path, l_globals, _, _, _, _) ->
                     pn _path;
                     pn "#%#%#%#%#%#%#%#%";
                     iterS Global.pprint "\n" l_globals) "\n\n") modules;

  (** function names sorted according to the new dependency *)
  let (sorted_functions, _, _, self_ref) = VcpDep.get_dependencies modules in
  pn_s "DONES" "Dependencies analysis finished";
  dbg "REC" "self ref:" (iterS p ", ") self_ref;

  let programs' : t F.t = get_programs modules in

  pn "~_~_~_~_~_~_~_~@@@@ Function Returning FuncPtr @@@@~_~_~_~_~_~_~_~";
  F.iter (fun _ (name, _, attr, (proc, _, _)) ->
      if List.exists
           (function Exp.FUNC (funcptrs, _) -> List.exists (function Exp.FUNCPTR (_, _) -> true| _ -> false) funcptrs | _ -> false) attr then
      begin
        
        pn name;
        Exp.print proc;
        pn ""
      end      
    ) programs';
  pn "~_~_~_~_~_~_~_~@@@@ ..... @@@@~_~_~_~_~_~_~_~";
  
  (modules, programs', sorted_functions, self_ref)
;;

let get_saved_specs slacDataDir =
  let filename = slacDataDir ^ "/saved_specs" in
  try
    let res : (Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t) F.t = read_file filename in
    pn ("Saved specs loaded: " ^ (string_of_int (F.cardinal res)));

    let ic = F.cardinal (F.filter (fun _ (_,_,(s,_),_) -> List.length s > 0) res) in
    pn ("Saved specs loaded (non void *): " ^ (string_of_int ic));
    
    F.iter (fun k (attr, params, (specs, _), body) ->
        if VcpPrecond2.is_void_pointer attr then pw "void *";
        pw k; pw "("; iterS Term.pprint ", " params; pn " )";
        let count = ref 0 in
        iterS (fun (r, (_,d,a), (s,_,b)) ->
            VcpPrecond2.print_specs !count k (r,s,d,a,b);
            count := !count + 1;
          ) "\n" specs;
        pn "") res; pn "";
    res
  with
    _ ->
    F.empty
;;


let save_specs slacDataDir topfunc specs =
  let filename = slacDataDir ^ "/saved_specs" in
  let specs' = F.filter (fun k (attr, _, (l_specs, _), _) -> not (k=topfunc) && (VcpPrecond2.is_void_pointer attr || List.length l_specs > 0)) specs in
  write_file filename specs';
  pn ("Number of saved specs: " ^ (string_of_int (F.cardinal specs')));
;;



let interatcive_process_ref curdir (programs_ref : EL.programs_t) =
  
  let is_running = ref true in
  while !is_running do
    pn "Enter command: 'f' for function lookup, 'q' for quit";
    let cmd = read_line () in
    if cmd = "q" then
      is_running := false
    else if cmd = "f" then
      begin
        try
          pn "Enter function name:";
          let fn = read_line () in
          let (raw_file, modulename, modulepath, originalpath) = EL.get_function programs_ref fn in
          pn originalpath;
          pn "Next action: (p) Print function, (t) Print with types, (d) dependency list result (n) Next";
          let ans = read_line () in
          (* if ans = "p" then
            Procedure.pprint (function_name, params, body)
          else if ans = "t" then
            begin
              let t = !Options.show_types in
              Options.show_types := true;
              Procedure.pprint (function_name, params, body);
              Options.show_types := t
            end
          else if ans = "d" then
            begin
              pn "Enter list of functions to be ignored (comma separated)";
              let s_ignores = read_line () in
              let l_ignores = split ',' s_ignores in
              let ls, _ = VcpDep.get_dependency_set_of_list ~mods:modules G.empty fn l_ignores in
              pi (List.length ls)
            end
          else *) if ans = "w" then
            begin
              let t1 = Sys.time () in
              let files = get_all_modulepaths curdir in
              List.iter (fun file ->
                  let filepath = curdir ^ "/" ^ file in
                  if Sys.is_directory filepath
                  then ()
                  else
                    begin
                      let (i, moduledata) : (int * VcpAllC.t) = read_file filepath in
                      let (filename, _, l_globals, _, _, _, _) = moduledata in
                      
                      List.iter (function Global.STATEMENT s ->
                                           let _ = VcpAllC.walk_body "*" [] programs_ref s in
                                           ()
                                        | _ -> ()) l_globals;
                    end
                ) files;
              Hashtbl.iter (fun (fname, v) fs ->
                  p fname; p " . "; p v; p " -> "; iterS p "," fs; pn ""
                ) VcpAllC.fp_store;
              
              let t2 = Sys.time () in
              pn ("Time (Global): " ^ (string_of_float (t2 -. t1)));

              VcpAllC.queue := fn::!VcpAllC.queue;
              let _ = VcpAllC.walk_Q programs_ref in

              let t3 = Sys.time () in
              pn ("Time: " ^ (string_of_float (t3 -. t2)));
              
              pn "Number of statements:";
              pi !VcpAllC.count;
              pn "Number of fp_ptr call:";
              pi !VcpAllC.fpptr;
              pn "STORE:";
              Hashtbl.iter (fun (fname, v) fs ->
                  p fname; p " . "; p v; p " ==> "; iterS p ", " fs; pn ""
                ) VcpAllC.fp_store;
              pn "HEAP:";
              Hashtbl.iter (fun (sname, fld) fs ->
                  p sname; p " -> "; p fld; p " ==> "; iterS p ", " fs; pn ""
                ) VcpAllC.fp_heap
            end
          else
            ()
        with
          Not_found ->
          pn "Not found"
      end
    else
      ()
  done
;;

let backup_specs = ref F.empty;;

let run_precond slacDataDir analyzed_functions programs self_ref all_structs global_store global_post current_function_group =
  if "ERR_put_error" |<- current_function_group then
    analyzed_functions
  else if List.length current_function_group > 1 || List.hd current_function_group |<- self_ref then 
    begin
      dbg "GC" "REC\n" print_gc $$ Gc.stat ();
      let l_res = VcpPrecond2.verify_rec current_function_group programs all_structs analyzed_functions global_post global_store all_structs in
      if not (List.for_all (fun (_, (attr,_,_,_)) -> VcpPrecond2.is_void_pointer attr) l_res) && List.length l_res = 0 then
        raise (StError "ZERO DISJUNCT");
      let analyzed_functions' = (fun af (k, v) -> F.add k v af) |->> (analyzed_functions, l_res) in
      backup_specs := analyzed_functions;
      save_specs slacDataDir !Options.functions !backup_specs;
      analyzed_functions'
    end
  else
    try
      (fun (analyzed_functions : (Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t) F.t) current_function ->
        let (module_path, (function_name, params, body)) =
          try
            EL.get_function_details programs current_function 
          with
            _ ->
            pn ("Missing Function: " ^ current_function);
            raise (StError "LIB-1")
        in
        let attr = Exp.get_attributes function_name in
        let param_names = (fun x -> Term.EXP x) |>>| ((VcpPrecond2.get_var_from_param "***") |>>| params) in
        if !Options.to_be_code_printed then
          begin
            pn module_path;
            Procedure.pprint (Exp.VAR(current_function,[]), params, body);
            pn "";
          end;
        
        pn_s "DONES" (current_function ^ " @ " ^ module_path);
        let ((specifications, d_s), bd) : VcpPrecond2.specs * VcpPrecond2.t =
          try
            begin
              dbg "GC" current_function print_gc $$ Gc.stat ();
              let structs = VcpPrecond2.get_structures current_function programs all_structs  in
              dbg "STRUCTS" (current_function ^ "::: ") (V.iter (fun sn s -> pw sn; p "->"; Structure.pprint s; p "\n")) structs;
              
              VcpPrecond2.verify module_path current_function (attr, params, body) analyzed_functions current_function_group global_post global_store structs programs
            end
          with
          | StError s -> pn s; ([], VcpPrecond2.false_d), VcpPrecond2.SKIP(Locs.dummy)
          | e -> raise e
        in
        
        if not (VcpPrecond2.is_void_pointer attr) && List.length specifications = 0 then
          raise (StError "ZERO DISJUNCT");
        
        let analyzed_functions' : (Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t) F.t = F.add current_function (attr, param_names, (specifications, d_s), bd) analyzed_functions in
        backup_specs := analyzed_functions';
        save_specs slacDataDir !Options.functions !backup_specs;
        
        analyzed_functions'
      ) |->> (analyzed_functions, current_function_group)
    with
      e ->
      if !Options.catch_exception then
        raise e
      else
        analyzed_functions
;;

let run_in_fork slacDataDir analyzed_functions programs self_ref all_structs global_store global_post current_function_group =
  
  let aux () =
    let pid = Unix.fork () in
    match pid with
    | 0 -> (* child process *)
       begin
         try
           let res = run_precond slacDataDir analyzed_functions programs self_ref all_structs global_store global_post current_function_group in
           write_file (slacDataDir ^ "/" ^ "analyzed_so_far") res;
           exit 0
         with
         | Sys_error mes -> failwith ("exception from child Sys_err " ^ mes)
         | _ -> failwith "exception from child"
       end
    | _ -> (* parent process *)
       begin
         try
           let (_,status) = Unix.wait () in
           match status with
           | Unix.WEXITED _ -> ()
           | _ -> 
              failwith "Exceptional case"
         with
         | _ ->
            failwith "deplist generating process was killed"
       end
  in
  aux ();
  let refres = read_file (slacDataDir ^ "/" ^ "analyzed_so_far") in
  refres
;;


let start slacDataDir =
  
  let curdir = slacDataDir ^ "/Translated" in
  if !Options.interactive then
    let _fmod : (int * VcpAllC.t) list = Ftools.read_allfiles (slacDataDir ^ "/Translated") in
    let modules = snd |>>| _fmod in
    let programs = get_programs modules in
    interatcive_process modules programs 
    
  else if !Options.interactive_ref then
    let files = get_all_modulepaths curdir in
    let programs_ref = build_programs_ref curdir files in
    interatcive_process_ref curdir programs_ref

  else
    if Sys.is_directory curdir then
      begin
        
        let manual_specs =
          let filename = !Options.manuals in
          if filename = "" then []
          else (* ConvFtoK.manual_input filename *) (* REVERT BACK *) []
        in

        (*
        let modules =
          if !Options.read_from <> "" then
            let modules : VcpAllC.t list = read_file !Options.read_from in
            modules
          else
            
            begin
              pn_s "DONES" "Analysis begins.";
              dbg "DONES" "Current directory:" p curdir;
              dbg "GC" "Program Started\n" print_gc $$ Gc.stat ();
              let gta1 = Sys.time () in

              
              dbg "GC" "Read finished\n" print_gc $$ Gc.stat ();
              
              let top_func = !Options.functions in

              if !Options.dump_to <> "" then
                begin
                  pn_s "DONES" "Starting from top level";
                  pause "FP Now";
                  let sp_tm = Spacetime.Series.create "/home/kmr/Documents/slacInputFiles/spacetime-sp" in
                  pause "FP Done";
                  let funcp_res = ConvFtoK.fp_top_level slacDataDir top_func sp_tm in
                  let gta2 = Sys.time () in
                  print_endline "Funcp: Done\n";
                  dbg "DONED" "Funcp time:" pn (string_of_float (gta2 -. gta1));
                  
                  let _Fdata = Ftools.read_allfiles (slacDataDir ^ "/Translated") in
                  pn_s "DONES" "Modules are loaded";
                  let gta3 = Sys.time () in
                  dbg "DONES" "Reading saved data and initializing necessary data:" pn (string_of_float (gta3 -. gta2));
                  
                  let modules' = snd |>>| _Fdata in

                  (* let showTime mes fsec =
                  let time_min:int = (int_of_float fsec) / 60 in
                  let time_h:int = time_min / 60 in
                  let time_m:int = time_min mod 60 in
                  let time_s = fsec -. (float_of_int (time_min * 60)) in
                  print_string mes; flush_all ();
                  print_endline (
                      (string_of_int time_h) ^ "h "
                      ^ (string_of_int time_m) ^ "m "
                      ^ (string_of_float time_s) ^ "s "
                    )
                in
                pf_s "FPAresult" (showTime "time (FPA): ") (gt6-.gta3);
                   *)
                  Spacetime.Series.save_and_close sp_tm ;

                  let modules'' =
                    print_endline "Start FP-translation ...";
                    let (sh, funpos) = funcp_res in                    
                    let result = funcp' funpos modules' in
                    print_endline "Done\n";
                    result
                  in
                  
                  pn_s "DONES" "Struct is generated";
                  pn_s "DONES" "Function pointer substitution is done";
                  dbg "GC" "After FPA Substitution" print_gc $$ Gc.stat ();
                  pf_s "SOURCEALL" (iterS (fun (_, _path, l_globals, _, _, _, _) ->
                                        pn _path;
                                        pn "#%#%#%#%#%#%#%#%";
                                        iterS Global.pprint "\n" l_globals) "\n\n") modules'';
                  modules''
                end
              else
                begin
                  let _fmod : (int * VcpAllC.t) list = Ftools.read_allfiles (slacDataDir ^ "/Translated")in
                  let modules' = snd |>>| _fmod in
                  pn_s "SOURCE" "\n*************************";
                  pf_s "SOURCE" (iterS (fun (_, _path, l_globals, _, _, _, _) ->
                                     pn _path;
                                     pn "#%#%#%#%#%#%#%#%";
                                     iterS Global.pprint "\n" l_globals) "\n\n") modules';

                  
    
                  modules'
                end
            end 
        in
         *)
        
        (* if !Options.dump_to <> "" then
          begin
            write_file !Options.dump_to (modules (* , all_structs *));
            pn ("Modules data is written to " ^ !Options.dump_to)
          end
        el  se (* TO BE MOVED BEFORE *) *)
        begin
            (** Handle saved specifications and unknown/to be skipped function names *)
          let saved_specs = if not !Options.recompute_specs then get_saved_specs slacDataDir else F.empty in
          Options.unknowns.contents <- !Options.unknowns @ get_manual_funcs manual_specs @ (F.fold (fun k v acc -> k::acc) saved_specs []) ;

          (** programs is the map from function name to its file name, params, body, and specifications *)
          let (modules_map, programs, sorted_functions, self_ref) = get_dependency_and_programs_ref curdir in

          let sorted_functions =
            begin
              pn_s "DONES" "Dependency list is reversed";
              List.rev sorted_functions
            end
          in
          dbg "DONES" "Number of sorted functions:" pl (List.length sorted_functions);
          dbg "DONES" "List of functions sets:" (iterS (fun fs -> p "{"; iterS p "," fs; p "}") ",") sorted_functions;
          pf_s "DEP" (List.iter (fun set -> begin p_s "DEP" "{"; pf_s "DEP" (iterS p ", ") set; p_s "DEP" "}"; if List.length set = 1 && List.hd set |<- self_ref then p_s "DEP" "*"  end)) sorted_functions;
          
          let rec is_diff_flds xs ys =
            match xs, ys with
              [], [] -> false
            | [], _ -> true
            | _, [] -> true
            | (x,_)::xs', (y,_)::ys' ->
               if Exp.toStr x = Exp.toStr y then
                 is_diff_flds xs' ys'
               else
                 true
          in
          
          let all_global_vars : Exp.t list =
            F.fold (fun _ compacted acc ->
                let (gl, _) = read_file compacted in
                let vs = List.concat ((fun g ->
                             match g with Global.STATEMENT s -> [VcpPrecond2.get_var_from_param ("GLOBAL",[]) s] | _ -> []) |>>| gl) in
                acc @@ vs
              ) modules_map []
              
          in
          
          VcpPrecond2.all_functions.contents <- (List.concat sorted_functions);

          backup_specs := saved_specs;

          let precond_analyze () =
            (**
               Task: Global Computation
             *)
            let (global_store, global_post, file_structures) =
              F.fold
                (fun c_filepath compacted (store, post, file_structures) ->
                  
                  let (gl, structures) : (Global.t list * Structure.t V.t) = read_file compacted in
                  
                  (* (fname, filepath, gl, structures, a, b, c) *)
                  let (global_store, (global_post : Formula.ut)) =
                    try
                      VcpPrecond2.execute_global gl store post ("GLOBAL", F.empty, [], all_global_vars, structures, programs)
                    with
                      e ->
                      pn ("\nGLOBAL ANALYSIS ERROR at ");
                      raise e
                  in
                  (global_store, global_post, (c_filepath, structures)::file_structures)
              ) modules_map (M.empty, VcpPrecond2.empty, []) in
            pn "Global execution is finished";

            dbg "DONES" "Global Post Condition:" Formula.pprint [global_post];
            dbg "DONES" "Global Store:" VcpPrecond2.m_print_s global_store;

            (**
                 Task: Compacting structures
             *)
            pn "ALLL";
            pi (List.length file_structures);
            let (g_structures, all_structs) = (fun (g_acc, l_acc) (c_filepath, structures) ->
                let g_acc', sts =
                  V.fold 
                    (fun sname ((_, flds, _) as s) (g_acc, acc) ->
                      let g_acc' =
                        if V.mem sname g_acc then
                          let (pfname, (_, pflds, _)) = V.find sname g_acc in
                          if pfname = "<>" then
                            g_acc
                          else if pfname = c_filepath then
                            if List.length flds > 0 then
                              V.add sname (c_filepath, s) (V.remove sname g_acc)
                            else
                              g_acc
                          else
                            if List.length flds = 0 then
                              g_acc
                            else if List.length pflds = 0 then
                              V.add sname (c_filepath, s) g_acc
                            else
                              if is_diff_flds pflds flds then
                                V.add sname ("<>", s) (V.remove sname g_acc)
                              else
                                g_acc
                        else
                          V.add sname (c_filepath, s) g_acc
                      in
                      
                      let acc' =
                        if V.mem sname acc then
                          if List.length flds > 0 then
                            V.add sname s (V.remove sname acc)
                          else
                            acc
                        else
                          V.add sname s acc
                      in
                      (g_acc', acc')
                    ) structures (g_acc, V.empty)
                in
                let l_acc' = V.add c_filepath sts l_acc in
                
                g_acc', l_acc'
              ) |->> ((V.empty, V.empty), file_structures)
            in

            let all_structs' =
              V.map (fun l_sts ->
                  V.filter (fun sname _ ->
                      if V.mem sname g_structures then
                        let (pfname, _) = V.find sname g_structures in
                        if pfname = "<>" then
                          true
                        else
                          false
                      else
                        raise (StError "Funny g_structures: not all structures added")
                    ) l_sts
                ) all_structs in
            
            let g_structures' = V.filter (fun _ (pfname, s) -> if pfname = "<>" then false else true) g_structures in
            let g_structures'' = V.map (fun (_, s) -> s) g_structures' in
            
            let all_structs = V.add "*" g_structures'' all_structs' in
            pause "ENTER";
            pn "ALL:";
            pi (V.cardinal g_structures);
            dbg "STRUCTS" "All structures are:" (V.iter (fun fname s ->
                                                     pn fname; pn "------------";
                                                     V.iter (fun _ s -> Structure.pprint s; p "\n") s)) all_structs;
            (**
                 Task: library function computation
             *)
            let library' : (Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t) F.t = get_manual_specs global_store programs manual_specs in
            let library = F.merge (fun k x1 x2 ->
                              match x1, x2 with
                                Some _, _ -> x1
                              | _, Some _ -> x2
                              | _, _ -> None
                            ) library' saved_specs in
            (fun (analyzed_functions : (Exp.attr list * Term.t list * VcpPrecond2.specs * VcpPrecond2.t) F.t) current_function_group ->
              pn "--*-*--";
              F.iter (fun fn _ -> pw fn) analyzed_functions; pn "";
              pn "--*-*--";
              run_in_fork slacDataDir analyzed_functions programs self_ref all_structs global_store global_post current_function_group
             
            ) |->> (library, sorted_functions) in
          
          if "NOP" |<- !p_opt then
            ()
          else
            begin
              VcpBuiltIn.init_builtins ();
              let res =
                try
                  precond_analyze ()
                with
                  e ->
                  save_specs slacDataDir !Options.functions !backup_specs;
                  raise e
              in
              save_specs slacDataDir !Options.functions res
            end
          
        end
        
        
      end
    else
      raise (Ftools.StError "Please select a valid directory")
;;
