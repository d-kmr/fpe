open Ftools
open VcpTranslate
open VcpBase
   
module G  = Map.Make(String)
          
type rec_t = NONREC of bytes | REC of bytes list

let get_dependency_0 body =
  let rec aux = function
    | Block.SKIP ->
       []
    | Block.ASSIGN (_, _, pr, _) ->
       aux pr
    | Block.IF (_, p1, p2, pr, _) ->
       aux p1 @@ aux p2 @@  aux pr
    | Block.WHILE (_, _, block, _, pr, _) ->
       aux block @@ aux pr
    | Block.CONS (_, _, pr, _) ->
       aux pr
    | Block.MUTATION (_, _, _, pr, _) ->
       aux pr
    | Block.LOOKUP (_, _, _, pr, _) ->
       aux pr
    | Block.DISPOSE (_, pr, _) ->
       aux pr
    | Block.PROCCALL (a, params, _, pr, _) when Bytes.length (Term.toStr a) > 0 && Bytes.sub (Term.toStr a) 0 1 <> "@" ->
       [(Term.toStr a, params)] @@ aux pr
    | Block.PROCCALL (a, _, _, d, _) ->
       aux d
    | Block.MALLOC (_, _, d, _) ->
       aux d
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
  aux body;; 

                                    
let get_calls modules : string list G.t =
  (fun acc (filename, fpath, l_globals, _, _, _, _) ->
   let l_globals' = (function Global.PROC _ | Global.FFILE _ -> true | _ -> false) |>- l_globals in
   (fun acc g ->
     match g with
      Global.PROC ((proc_name, _, body), _, _, _,  _) ->
       let fnames = fst |>>| get_dependency_0 body in
       G.add (Exp.toStr proc_name) fnames acc
     | Global.FFILE (st, fn) ->
        begin
          let fin = open_in st in
          let g : Global.t = Marshal.from_channel fin in
          close_in fin;
          match g with
            Global.PROC ((proc_name, _, body), _, _, _,  _) ->
             let fnames = fst |>>| get_dependency_0 body in
             G.add (Exp.toStr proc_name) fnames acc
          | _ -> acc
        end
     | _ -> acc
   ) |->> (acc, l_globals')
  ) |->> (G.empty, modules)
;;

let get_filtered_call calls func_name knownlist =
  
  let rec aux prevs func =
    try
      dbg "DEPS" "func:" p func;
      let fnames = try
          List.sort_uniq Bytes.compare $$ G.find func calls
        with
          Not_found -> raise (StError "Not found in 'get_filtered_call' (2050)")
      in
      
      let fnames'' = (fun f -> not (f |<- knownlist)) |>- fnames in
      let fnames' = (fun f -> not (f |<- prevs)) |>- fnames'' in

      dbg "DEPS" "~>" (iterS p ",") fnames; 
      
      let res, prevs' = (fun (acc, prevs) f ->
          let res, prevs = aux (f::prevs) f in
          acc @ res, prevs
        ) |->> (([], prevs), fnames')
      in
      
      (func, fnames'')::res, prevs'
    with
      _ -> [], prevs
  in
  dbg "DEPS" "top-level:" p func_name;
  let res, _ = aux [func_name] func_name in
  res
;;

let rec refine all c' (c : bytes list list) =
  match c with
    [] -> c'
  | x::xs ->
     if List.length x = 1 && List.hd x |<- (List.concat xs) then
       refine all c' xs
     else
       let pred, succ = List.partition (fun ys ->
                            List.exists (fun y ->
                                let zs = try
                                    snd $$ List.find (fun (z',_) -> z' = y) all
                                  with
                                    Not_found ->
                                    pn y;
                                    iterS pw "," (fst |>>| all);
                                    raise (StError "Not found in 'refine' (2047)")
                                in
                                List.exists (fun x' -> x' |<- zs) x
                              ) ys                            
                          ) xs in
       let pred' = refine all [] pred in
       
       refine all (c' @ pred' @ [x]) succ;;

let rec part f acc = function
    [] -> None, List.rev acc
  | x::xs -> if f x then Some x, List.rev acc @ xs else part f (x::acc) xs
;;

let rec get_cycles (visited : string list) (current : string) (stable : string list) (calls : (string * string list) list) (cycles : string list list) cont =
    (**
     *  Input:
     *     1. visited: already visited
     *  Output:
     *     1. all the cycles: initially [], final result
     *     2. if cycle is found then current else ...
     *     3. all the functions whose dependency list is already prepared
              it includes well-formed cycles, too.
     *     4. remaining function calls from each of the functions
     *     5. If it is among stable
     *)
  dbg "DEPS" "\nCurrent:" p current;
  dbg "DEPS" "Visited:" (iterS p ",") visited;
  dbg "DEPS" "Stable:" (iterS p ",") stable;
  dbg "DEPS" "Cycle:" (iterS (iterS p ",") "|") cycles;
  

  let (cycles, l_current, stable, calls, flag) =
  if current |<- stable then 
    begin
      (** if the current function is in stable list then all its dependencies are already calculated. So, nothing to calculate *)
      (* let _ = List.find (fun f -> f = current) stable in *)
      pn_s "DEPS" (current ^ " is stable.");
      if current |<- cont then
        begin
          (cycles, [current], stable, calls, false)
        end
      else
        (cycles, [], stable, calls, true)
    end
  else
    try
      begin
        (** the current function is not in stable. So let's compute it *)
        (** 1. detect the cycle *)
        if current |<- visited then
          begin
            (** cyclic reference found. Stop calculation. Return cyclic reference *)
            (* pn ("****** Current is in visited; A cycle reference found at " ^ current); *)
            pn_s "DEPS" ("Cycle found @ " ^ current);
            cycles, [current], stable, calls, false
          end
        else
          (** cyclic reference not found at the current function *)
          begin
            pn_s "DEPS" ("Cycle NOT found @ " ^ current);
            (* pn ("Current is not in visited; Cycle reference isn't found at " ^ current); *)
            let matched, unmatched = part (fun (f, _) -> f = current) [] calls in
            let res = ref true in
            match matched with
            | Some (_, gs) ->
               let gs = List.sort_uniq Bytes.compare gs in
               dbg "DEPS" "gs:" (iterS pw ",") gs;
               pn_s "DEPS" "current function will be analyzed by calling other functions in the body";
               (** current function will be analyzed by calling other functions in the body *)

               let (c, f, a, b, j) =
                 (fun (c, f, a, b, j) g ->
                   dbg "DEPS" "Now let's visit " p g;
                   (** get the updated lists and if a cycle is found *)
                    (** c'=cycles. f'=[]. a'=stable group of function. b'=calls. j=false *)
                   let (c', f', a', b', j) = get_cycles (current::visited) g a b c (f@cont) in
                   dbg "DEPS" "Back to" p current;
                   (**
                      There are four categories of result.
                      a. f = [] and f' = []
                      no cycle reference found from analyzing g and no reference found from previous analysis inside current function.  
                      Just add singleton to the "Cycles" and keep TEMP <= []
                      b. f != [] and f' = []
                      no cycle reference found from analyzing g and    reference found from previous analysis inside current function.  
                      Just add singleton to the "Cycles" and keep TEMP <= f
                      c.
                    *)
                   if f' = [] then
                     begin
                       (** if no cycle found return cycle info from other function calls *)
                       (** add a singleton cycle *)
                       if not j then
                         begin
                           pn_s "DEPS" (g ^ " (local) is added as singleton to 'Result' since there is no cycle from it and it is not already added");
                           (* p "j is false. "; p g; p " is added to {"; iterS (iterS p ",") ";" c'; pn "}"; *)
                           ([[g]] @@ c', f, a',b',j)
                         end
                       else
                         begin
                           pn_s "DEPS" (g ^ " (local) is not added to 'cycles' since it is already visited (flag=true) and taken care of at elsewhere");
                           (c', f, a',b',j)
                         end
                     end
                   else
                     if current |<- f' then
                       begin
                         pn_s "DEPS" ("@@@@ Cycle Complete for " ^ current ^ " on " ^ g);
                         (** if cycle is found and this is the cyclic reference then just pass the cycle info from previous calls *)
                         (** add the full cycle *)
                         (c', f @@ f', a', b',j)
                           (* (c', f @@ f', a', b',j) *)
                       end
                     else
                       begin
                         res := false;
                         pn_s "DEPS" ("@@@@ Cycle Found on " ^ g ^ " in " ^ current);
                         (** if cycle is found and this is not the cyclic reference then just pass the cyclic info including itself. *)
                         (c', f @@ f', a', b',j)
                       end
                 ) |->> ((cycles, [], stable, unmatched, false), gs) in
               let a' = [current] @@ a in
               
               let (c, f, a, b, j) =
                 if f = [] then (** no cycle is found from any of its function call *)
                   (c, f, a', b, false)
                 else
                   if current |<- f then
                     if !res = true && List.length (common visited f) = 0 then (** cycle found implies cycle complete *)
                       let a' = f @@ a' in
                       (f::c, [], a', b, true)
                       
                     else                (** SPECIAL *)
                       (c, [current] @@ f, a', b, false)
                   else                  (** Some cycle is found and incomplete. So add current to the cycle *)
                     (c, [current] @@ f, a', b, false)
               in
               p_s "DEP" "@";
               (* p "{"; iterS (iterS p ",") ";" c; pn "}"; *)
               (c, f, a, b, j)
            | None ->
               pn ("@@@@@@ Not found " ^ current); 
               (cycles, [], stable, unmatched, false)
            end
      end
    with
      _ ->
      ([], [], [], [], false)
  in

  dbg "DEPS" "l_current:" (iterS p ",") l_current;
  
  (cycles, l_current, stable, calls, flag)
;;

let get_all_dependencies mains nonmains =
  dbg "DEPS" "|mains|:" pl (List.length mains);
  dbg "DEPS" "|nonmains|:" pl (List.length nonmains);
  let (c, _, a, b, _) =
    (fun (c, _, a, all, j) (current, _) ->
      pn_s "DEPS" ""; p_s "DEPS" current; p_s "DEPS" "~>";
      
      let (p,q,r,s,j) = get_cycles [] current a all c [] in
      
      if j then
        begin
          pn_s "DEPS" "STABLE";
          (p,q,r,s,j)
        end
      else
        begin
          pn_s "DEPS" "Non-STABLE";
          ([[current]] @ p,q,r,s,j)
        end
    ) |->> (([], [], [], mains @ nonmains, false), mains) in
  pn ("Now rest started ");
  (* pn_s "DEP" "All except rest";
  pf_s "DEP" (iterS (fun gs -> p "{"; iterS pw "," gs; p "}") "\n") c; *)
  let rec rest (c, f, a, b, j) =
    match b with
      [] -> (c, f, a, b, j)
    | (x::xs) ->
       
       let xi = fst x in
       
       p_s "RES" "start new"; pn_s "RES" xi;
       let (c, f, a, b, j) = get_cycles [] xi a b c [] in
       p_s "DEPS" "*";
         if not j then
           rest (f::c, [], a, b, j)
         else
           rest (c, [], a, b, j)
  in

  let (c, _, a, b, _) = rest (c, [], a, b, false) in
  pn "rest is finished";
  (c,a,b)
;;
  
let get_dependency_set_of_list ?mods:(modules=[]) saved_calls func_name knownlist =
  (* p_opt := ["DEP"]; *)

  let calls : bytes list G.t =
    
    if G.cardinal saved_calls = 0 (* && List.length modules > 0 *) then
      begin
        pn "modules are provided";
        let res = get_calls modules in
        (* write_file "calls" res ; *)
        (* saved_calls := res; *)
        res
      end
    else(
      pn "Saved data are read";
      (* read_file "calls" *)
      saved_calls
    )
  in
  pw "Number of functions:";
  pi (G.cardinal calls);
  match get_filtered_call calls func_name knownlist with
    mains'::nonmains'  ->
     let mains = (fun (f, gs) -> (f, (fun g -> G.mem g calls) |>- gs)) mains' in
     let nonmains = List.sort_uniq  (fun (x,_) (y,_) -> Bytes.compare x y) ((fun (f, gs) -> (f, List.sort_uniq Bytes.compare ((fun g -> G.mem g calls) |>- gs))) |>>| nonmains') in
     
     pn_s "DEP" "Functions Calls (mains):";
     pf_s "DEP" (fun (f, gs) -> p f; p "->"; iterS p "," gs; pn "") mains;
     pn_s "DEP" "Functions Calls (non-mains):";
     pf_s "DEP" (List.iter (fun (f, gs) -> p f; p "->"; iterS p "," gs; pn "")) nonmains;
     let all = (mains::nonmains) in
     let (c,a,b) = get_all_dependencies [mains] nonmains in
     
     let c' = (refine all [] c) in
     
     let deplist = (
         function f::[] as s ->
                   if G.mem f calls then
                     if f |<- G.find f calls then
                       REC s
                     else
                       NONREC f
                   else
                     raise (StError "Not found in dep list generation (2145)")
                | s -> REC s
       ) |>>| c' in
     
     iterS (function REC xs -> p "{"; iterS p ", " xs; p "}" | NONREC x -> p x) "\n" deplist; pn "";
     (deplist, calls)
  | _ -> ([], calls)
;;

let get_mains_nonmains calls fs =
  let fs_map    = Array.of_list fs in
  Array.sort Bytes.compare fs_map;
  pn_s "DEP" "Array is sorted";
  let index key =
    let rec aux l u =
      if l > u then raise (StError ("INDEX:" ^ key)) else
        let m = (l+u) / 2 in
        let o = Bytes.compare (Array.get fs_map m) key in
        if o == 0 then m
        else if o > 0 then
          aux l (m-1)
        else
          aux (m+1) u
    in
    aux 0 ((Array.length fs_map) - 1)
  in
  let fs_matrix = Array.make_matrix (List.length fs) (List.length fs) false in
  pn_s "DEP" "Matrix is prepared";

  List.iter (fun (f, gs) -> 
      List.iter (fun g -> 
          let gi = index g in
          if gi = -1 then
            ()
          else
            try Array.set (Array.get fs_matrix (index f)) (index g) true
            with
              _ -> pw "VCPALLC error:"; pl (index f); pi (index g) 
        ) gs) calls;

  pf_s "DEPS" (List.iter pw) fs;
  pf_s "DEPS" (Array.iter (fun m ->
      Array.iter (fun v -> if v then pw "T" else pw "F") m;
      pn ""
    )) fs_matrix;
  pf_s "DEPS" (List.iter pn) fs;

  pn_s "DEP" "Array is extended";
  (* let get i j = Array.get (Array.get fs_matrix i) j in *)
  let col i   = Array.map (fun arr -> Array.get arr i) fs_matrix in
  let for_all f = Array.fold_left (fun a x -> a && f x) true in
  let mains, nonmains =
    List.partition
      (fun (f, gs) ->
        let fi = index f in
        for_all (fun x -> x) (Array.mapi (fun i x -> not x || i = fi) (col (index f))))
      calls in
  (mains, nonmains);;


let get_preparation_data ?is_fp:(fp=true) modules =
    (** List of functions with their dependencies in the project *)
  let deps' : (string list * (string * string list) list) list = 
    let count = ref 1 in
    (fun (filename, fpath, l_globals, _, _, _, _) ->
      (** List of all functions with their dependencies in a file *)
      dbg "MOD" ((string_of_int !count) ^ ": ") p fpath;
      count.contents <- !count + 1;
      let deps' : (string list * string list) list =
        ((fun g ->
          match g with
            Global.PROC ((proc_name, _, program), _, _, _,  _) ->
            (** Get first degree of procedure dependencies including itself *)
            dbg "DEPROG" "DC. Dependency checking for " Exp.pprint proc_name;
            let procs' : string list =
              (* if fp then
                get_dependency_0_fp program
              else *)
                fst |>>| get_dependency_0 program
            in
            (** Change "main" to "<filename>-main" *)
            let proc_name = (* if Var.to_str proc_name = "main" then "main@" ^ (Bytes.sub filename 0 (Bytes.length filename - 2)) else *) Block.__N proc_name in
            ([proc_name], procs')
          | Global.FFILE (st, fn) ->
             begin
             let fin = open_in st in
             let g : Global.t = Marshal.from_channel fin in
             close_in fin;
             match g with
               Global.PROC ((proc_name, _, program), _, _, _,  _) ->
                let procs' : string list =
                  (* if fp then
                    get_dependency_0_fp program
                  else *)
                    fst |>>| get_dependency_0 program
                in
            (** Change "main" to "<filename>-main" *)
            let proc_name = (* if Var.to_str proc_name = "main" then "main@" ^ (Bytes.sub filename 0 (Bytes.length filename - 2)) else *) Block.__N proc_name in
            ([proc_name], procs')
             | _ -> ([], [])
             end
          | _ ->
             ([], [])
        ) |>>| l_globals) in
      let deps' : (string * string list) list = (fun (x, y) -> List.hd x,y) |>>| ((fun (x, _) -> x != []) |>- deps') in
      let fs, deps' = (fst |>>| deps'), deps' in
      p_s "DEP" "-";
      fs, deps'
    ) |>>| modules in
  pn_s "DONES" "Level 1 of dependency analysis is done";
  
  (** List of functions and List of functions with their dependencies *)
  let (fs', deps') : (string list list * (string * string list) list list) = List.split deps' in

  (** Flattening the list: a map from a function to its first degree of dependencies *)
  let calls' : ((string * string list) list) = List.concat deps' in
  pn_s "DEP" "function names are sorted";
  let s_calls : string list = fst |>>| calls' in

  if "TSORT" |<- !Ftools.p_opt then
    begin
      iterS (fun (s, ds) ->
          iterS (fun d -> pw s; pn d) "" ds
        ) "" calls'
    end
  ;
  
  if "MISSING" |<- !Ftools.p_opt then
    begin
      List.iter (fun (fn, gs) ->
          pn_s "MISSING" ("!" ^ fn ^ "->");
          let r = (fun g -> not ( g |<- s_calls )) |>- gs in
          if List.length r = 0 then
            pn_s "DEPROG" ("ALL CALL OK @ " ^ fn)
          else
            begin
              pn_s "MISSING" ("MISSING @ " ^ fn);
              iterS p "," r;
              pn ""
            end;
        ) calls';
      let missing =
        List.concat (
            ((fun (fn, gs) ->
              (* pn_s "MISSING" ("!" ^ fn ^ "->"); *)
              let r = (fun g -> not ( g |<- s_calls )) |>- gs in
              r
            )) |>>| calls') in
      pn "*********************";
      iterS pw "\n" (List.sort_uniq Bytes.compare missing);
    end;
  
  let fs = List.sort_uniq Bytes.compare (List.concat fs') in
  let calls = List.sort_uniq  (fun (x,_) (y,_) -> Bytes.compare x y) ((fun (f, gs) -> (f, List.sort_uniq Bytes.compare ((fun g -> g |<- fs) |>- gs))) |>>| calls') in
    
    (** List of functions (? how it is different than fs' except flattening ?) *)
  
  pn_s "DEP" "Going to analyze the dependencies";
  

  pn_s "DEP" "calls are sorted";
  pf_s "CALLS" (iterS (fun (f, gs) ->
                    p "void "; p f; p "(){"; iterS (fun g ->
                                                 p g; p "();"
                                               ) " " gs; pn "}"
                  ) "") calls;
  let (mains, nonmains) = get_mains_nonmains calls fs in

  pn_s "DEP" "Functions Calls (mains):";
  pf_s "DEP" (List.iter (fun (f, gs) -> p f; p "->"; iterS p "," gs; pn "")) mains;
  pn_s "DEP" "Functions Calls (non-mains):";
  pf_s "DEP" (List.iter (fun (f, gs) -> p f; p "->"; iterS p "," gs; pn "")) nonmains;
  (mains, nonmains, calls', calls)
;;



let get_dependencies modules =
  let (mains, nonmains, calls', calls) = get_preparation_data modules in
  
  let (c,a,b) = get_all_dependencies mains nonmains in

  let recs = fst |>>| ((fun (s, sl) -> (s |<- sl)) |>- calls') in

  let ggg x = (fun y ->
          let zs = snd $$ List.find (fun (z',_) -> z' = y) calls in
          List.exists (fun x' -> x' |<- zs) x
        ) in
  
  let fff x = (fun ys ->
      List.exists (ggg x) ys                            
    )
  in
  
  let rec refine c' (c : bytes list list) =
    match c with
      [] -> c'
    | x::xs ->
       
       if List.length x = 1 && List.hd x |<- (List.concat xs) then
           refine c' xs
       else
         let pred, succ = List.partition (fff x)  xs in
         let pred' = refine [] pred in
       
         refine (c' @ pred' @ [x]) succ
  in
  
  let c' = (refine [] c) in

  pn_s "DEP" "";
  pn_s "DEP" "\nAll are in descending order";
  pf_s "DEP" (iterS (fun gs -> p "{"; iterS p ", " gs; p "}"; if List.length gs=1 && List.hd gs |<- recs then pn "*" else pn "") "") c';

  (c',a,b, recs);;


(** --------------------------------------------------- *)

let get_preparation_data ?is_fp:(fp=true) (call_graph : bytes list G.t) =
  (** Flattening the list: a map from a function to its first degree of dependencies *)
  let calls' : ((string * string list) list) = G.bindings call_graph in
  let fs' = fst |>>| calls' in
  pn_s "DEP" "function names are sorted";
  let s_calls : string list = fst |>>| calls' in

  if "TSORT" |<- !Ftools.p_opt then
    begin
      iterS (fun (s, ds) ->
          iterS (fun d -> pw s; pn d) "" ds
        ) "" calls'
    end
  ;
  
  if "MISSING" |<- !Ftools.p_opt then
    begin
      List.iter (fun (fn, gs) ->
          pn_s "MISSING" ("!" ^ fn ^ "->");
          let r = (fun g -> not ( g |<- s_calls )) |>- gs in
          if List.length r = 0 then
            pn_s "DEPROG" ("ALL CALL OK @ " ^ fn)
          else
            begin
              pn_s "MISSING" ("MISSING @ " ^ fn);
              iterS p "," r;
              pn ""
            end;
        ) calls';
      let missing =
        List.concat (
            ((fun (fn, gs) ->
              (* pn_s "MISSING" ("!" ^ fn ^ "->"); *)
              let r = (fun g -> not ( g |<- s_calls )) |>- gs in
              r
            )) |>>| calls') in
      pn "*********************";
      iterS pw "\n" (List.sort_uniq Bytes.compare missing);
    end;
  
  let fs = List.sort_uniq Bytes.compare fs' in
  let calls = List.sort_uniq  (fun (x,_) (y,_) -> Bytes.compare x y) ((fun (f, gs) -> (f, List.sort_uniq Bytes.compare ((fun g -> g |<- fs) |>- gs))) |>>| calls') in
    
    (** List of functions (? how it is different than fs' except flattening ?) *)
  
  pn_s "DEP" "Going to analyze the dependencies";
  

  pn_s "DEP" "calls are sorted";
  pf_s "CALLS" (iterS (fun (f, gs) ->
                    p "void "; p f; p "(){"; iterS (fun g ->
                                                 p g; p "();"
                                               ) " " gs; pn "}"
                  ) "") calls;
  let (mains, nonmains) = get_mains_nonmains calls fs in

  pn_s "DEP" "Functions Calls (mains):";
  pf_s "DEP" (List.iter (fun (f, gs) -> p f; p "->"; iterS p "," gs; pn "")) mains;
  pn_s "DEP" "Functions Calls (non-mains):";
  pf_s "DEP" (List.iter (fun (f, gs) -> p f; p "->"; iterS p "," gs; pn "")) nonmains;
  (mains, nonmains, calls', calls)
;;


let get_dependencies2 call_graph =
  let (mains, nonmains, calls', calls) = get_preparation_data call_graph in
  
  let (c,a,b) = get_all_dependencies mains nonmains in

  let recs = fst |>>| ((fun (s, sl) -> (s |<- sl)) |>- calls') in

  let ggg x = (fun y ->
          let zs = snd $$ List.find (fun (z',_) -> z' = y) calls in
          List.exists (fun x' -> x' |<- zs) x
        ) in
  
  let fff x = (fun ys ->
      List.exists (ggg x) ys                            
    )
  in
  
  let rec refine c' (c : bytes list list) =
    match c with
      [] -> c'
    | x::xs ->
       
       if List.length x = 1 && List.hd x |<- (List.concat xs) then
           refine c' xs
       else
         let pred, succ = List.partition (fff x)  xs in
         let pred' = refine [] pred in
       
         refine (c' @ pred' @ [x]) succ
  in
  
  let c' = (refine [] c) in

  pn_s "DEP" "";
  pn_s "DEP" "\nAll are in descending order";
  pf_s "DEP" (iterS (fun gs -> p "{"; iterS p ", " gs; p "}"; if List.length gs=1 && List.hd gs |<- recs then pn "*" else pn "") "") c';

  (c',a,b, recs);;
