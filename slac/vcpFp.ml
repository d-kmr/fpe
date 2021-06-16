open Ftools
open VcpBase
open VcpTranslate

module P2 = Block
module E = Exp
module V = Var
module F = Map.Make(String)

module PV = struct
  type t = VR of V.t | LC of string * int

  let compare t1 t2 =
    match t1, t2 with
      VR (vn1, attr1), VR (vn2, attr2) ->
      let r1 = Bytes.compare vn1 vn2 in
      if r1 = 0 then
        if Var.GLOBAL |<- attr1 then
          -1
        else
          1
      else
        r1
    | LC (fn1, pos1), LC (fn2, pos2) ->
       let r = Bytes.compare fn1 fn2 in
       if r = 0 then
         pos1 - pos2
       else
         r
    | VR _, _ -> -1
    | _, _ -> 1
end;;

module Loc = struct
  type t = Exp.t * string (** location and field name *)

  let compare (p1,f1) (p2,f2) =
    let r = Exp.compare p1 p2 in
    if r = 0 then
      Bytes.compare f1 f2
    else
      r
end;;

module S = Map.Make(PV)
module H = Map.Make(Loc)

exception ModuleNotFound
exception NotFound of string
exception WrongType of string

type proc = string
type t = INTV of Exp.t * Exp.t | FUNS of proc list
type s = t S.t
type h = t H.t

let global = ""
let ptr = "*"
let ret = ("@ret",[])

(*
let is_var (_, e) =
  match e with
    Exp.VAR _ -> true
  | Exp.CONST _ -> false
  | _ -> raise (WrongType "Neither var nor location")
 *)

let eval_var s x : t =
  S.find (PV.VR x) s

let get_funs s fn l : proc list =
  let r = S.find (PV.LC (fn, l)) s in
  match r with
    FUNS fns -> fns
  | _ -> raise (WrongType "Found function pointer but required simple type")

let set_var (x:V.t) (t:t) (s:s) =
  let s' = S.remove (PV.VR x) s in
  S.add (PV.VR x) t s'

let enumerate x a b =
  match a,b with
    E.CONST a, E.CONST b ->
    let rec f acc i =
      if i <= b then
        f ((x, E.CONST b)::acc) (i+1)
      else acc
    in
    let res = f [] a in
    true, res
  | _, _ -> false, []

let rec all_combs xss =
  match xss with
    [] -> []
  | [xs] -> (fun x -> [x]) |>>| xs
  | xs::xss ->
     let xss' = all_combs xss in
     let rs = (fun x -> 
         let r = (fun xs' -> x::xs') |>>| xss' in
         r
       ) |>>| xs in
     List.concat rs
(*
let set_loc (s,h) (p:proc) (l:Exp.t) =
  try
    let (p', r) = get_loc p (s,h) (E.VAR x) in
    match r with
      INTV (l,u) ->
      let l' = if Exp.compare l v < 0 then l else v in
      let u' = if Exp.compare v u < 0 then u else v in
      let s' = S.remove (p', E.VAR x) s in
      let s'' = S.add (p',E.VAR x) (INTV (l',u')) s' in
      (s'',h)
    | _ ->
       raise (WrongType "Found simple type but required function pointer")
  with
    _ ->
    let s' = S.add (p, E.VAR x) (INTV (v,v)) s in
    (s',h)
 *)


let add_fn_s s (p:proc) (l:int) (f:proc list) =
  try
    let fs = get_funs s p l in
    let fs' = fs@f in
    let s' = S.remove (PV.LC (p, l)) s in
    let s'' = S.add (PV.LC (p, l)) (FUNS fs') s' in
    s''
  with
    _ ->
    let s' = S.add (PV.LC (p,l)) (FUNS f) s in
    s'



let lookup (_,h) (lc,f) : t =
  H.find (lc,f) h

(*
let mutate (s,h) (lc,f) v =
  try
    match lookup (s,h) (lc,f) with
      INTV (l,u) ->
      let l' = if Exp.compare l v < 0 then l else v in
      let u' = if Exp.compare v u < 0 then u else v in
      let h' = H.remove (lc,f) h in
      let h'' = H.add (lc,f) (INTV (l',u')) h' in
      (s,h'')
    | _ ->
       raise (WrongType "Found simple type but required function pointer")
  with
    _ ->
    let h' = H.add (lc,f) (INTV (v,v)) h in
    (s,h')

let add_h (s,h) (lc,fld) (f:proc) =
  try
    let r = lookup (s,h) (lc,fld) in
    match r with
      FUNS fs ->
      let fs' = f::fs in
      let h' = H.remove (lc, fld) h in
      let h'' = H.add (lc,fld) (FUNS fs') h' in
      (s,h'')
    | _ ->
       raise (WrongType "Found function pointer but required simple type")
  with
    _ ->
    let h' = H.add (lc,fld) (FUNS [f]) h in
    (s,h')
 *)

let rec (@<=) a b =
  match a,b with
    E.CONST c1, E.CONST c2 -> c1 <= c2
  | E.BINOP (p1, Op.ADD, e1), E.BINOP (p2, Op.ADD, e2) when p1=p2 -> e1 @<= e2
  | _ -> false

let rec (@<) a b =
  match a,b with
    E.CONST c1, E.CONST c2 -> c1 < c2
  | E.BINOP (p1, Op.ADD, e1), E.BINOP (p2, Op.ADD, e2) when p1=p2 -> e1 @< e2
  | _ -> false

let _C i = E.CONST i

let (@+) a b = E.op a b Op.ADD
let (@-) a b = E.op a b Op.SUB

let eval_h (s,h) (a,b) fld =
  let locs =
    H.fold (fun (x,_) v acc ->
        if a @<= x && x @<= b then
          x::acc
        else
          acc
      ) h []
  in
  if List.length locs > 0 then
    let (l,u) =
      (fun (l,u) x ->
        let l' = if l @<= x then l else x in
        let u' = if x @<= u then u else x in
        (l',u')
      ) |->> ((List.hd locs, List.hd locs), List.tl locs)
    in
    (lookup (s,h) (l,fld), lookup (s,h) (u,fld))
  else
    raise (NotFound ("Heap Eval Fails for [" ^ (Exp.toStr a) ^ "," ^ (Exp.toStr b) ^ "]" ))

let rec eval (s,h) = function
    E.CONST _ as e -> INTV (e, e)
  | E.VAR x -> eval_var s x
  | E.BINOP (e1, op, e2) as e ->
     begin
       let e1' = eval (s,h) e1 in
       let e2' = eval (s,h) e2 in
       match e1', e2' with
         INTV (l1, u1), INTV (l2, u2) ->
         begin
           match op with
             Op.MUL ->
             let combs = [E.op l1 u2 Op.MUL;E.op l2 u1 Op.MUL;E.op l2 u2 Op.MUL] in
             let l3 = E.min |->> (E.op l1 u1 Op.MUL, combs) in
             let u3 = E.max |->> (E.op l1 u1 Op.MUL, combs) in
             INTV (l3, u3)
           | Op.DIV ->
              if _C 0 @< l2 then
                INTV (E.op l1 l2 Op.DIV, E.op u1 l2 Op.DIV)
              else if u2 @< _C 0 then
                INTV (E.op u1 u2 Op.DIV, E.op l1 u2 Op.DIV)
              else
                INTV (E.NEGINF, E.POSINF)
           | Op.MOD ->
              INTV (_C 0, E.op u2 (_C 1) Op.SUB)
           | _ ->
              INTV (E.op l1 l2 op, E.op u1 u2 op)
         end
       | _, _ ->
         raise (NotFound ("Wrong eval execution " ^ (Exp.toStr e)))
     end
  | E.UNDEF -> INTV (E.NEGINF, E.POSINF)
  | e -> raise (NotFound ("Not supported eval " ^ (Exp.toStr e)))

let eval_t (s,h) t : t =
  match t with
    Term.NULL -> INTV (E.CONST 0, E.CONST 0)
  | Term.EXP e -> eval (s,h) e

let rec eval_b (s,h) b =
  match b with
    BExp.UNIT (t1, op, t2) ->
    begin
      let t1' = eval_t (s,h) t1 in
      let t2' = eval_t (s,h) t2 in
      match op with
        Op.EQ -> Some (t1' = t2')
      | Op.NE -> Some (t1' != t2')
      | Op.LE ->
         begin
           match t1',t2' with
             INTV (E.CONST l1, E.CONST u1), INTV (E.CONST l2, E.CONST u2) ->
             Some (l1 < u1 && l2 < u2)
           | _, _ -> None
         end
      | _ -> None
    end
  | BExp.OP (b1, op, b2) ->
     let b1' = eval_b (s,h) b1 in
     let b2' = eval_b (s,h) b2 in
     begin
       match op, b1',b2' with
         Op.AND, Some b1'', Some b2'' -> Some (b1'' && b2'')
       | Op.OR, Some b1'', Some b2'' -> Some (b1'' || b2'')
       | _ -> None
     end
  | _ -> None

let eval_fld (s,h) (t:E.t) fld =
  match eval (s,h) t with
    INTV (l,u) ->
    eval_h (s,h) (l,u) fld
  | _ ->
     raise (NotFound ("Not supported eval_ptr "))

let eval_ptr (s,h) (t:E.t) = eval_fld (s,h) t ptr

let intv (i1:t) (i2:t) =
  match i1, i2 with
    INTV (x1,y1), INTV (x2,y2) ->
    INTV (min x1 x2, max y1 y2)
  | _, _ -> raise (WrongType "Type mismatch in intv")

(*
let s_union s1 s2 x =
  if S.mem x s1 then
    if S.mem x s2 then
      intv (S.find x s1) (S.find x s2)
    else
      S.find x s1
  else
    S.find x s2
 *)

(*
let h_union h1 h2 x fld =
  if H.mem (x,fld) h1 then
    if H.mem (x,fld) h2 then
      intv (H.find (x,fld) h1) (H.find (x,fld) h2)
    else
      [H.find (x,fld) h1]
  else
    [H.find (x,fld) h2]
 *)

let s_cup_s s1 s2 =
  S.merge (fun x v1 v2 ->
      match v1, v2 with
        Some v1', Some v2' ->
        Some (intv v1' v2')
      | None, _ -> v2
      | _, _ -> v1
      
    ) s1 s2

let h_cup_h h1 h2 =
  H.merge (fun x v1 v2 ->
      match v1, v2 with
        Some v1', Some v2' ->
        Some (intv v1' v2')
      | None, _ -> v2
      | _, _ -> v1
    ) h1 h2

let r_union (s1,h1) (s2,h2) =
  (s_cup_s s1 s2, h_cup_h h1 h2)

let next_pr = function
    P2.SKIP -> P2.SKIP
  | P2.ASSIGN (_, _, pr, _)
  | P2.LOOKUP (_, _, _, pr, _)
  | P2.MUTATION (_, _, _, pr, _)
  | P2.IF (_, _, _, pr, _)
  | P2.WHILE (_, _, _, pr, _)
  | P2.CONS (_, _, pr, _)
  | P2.DISPOSE (_, pr, _)
  | P2.PROCCALL (_, _, pr, _)
  | P2.BLOCK (_, pr, _)
  | P2.DECL (_, _, _, pr, _)
  | P2.MALLOC (_, _, _, pr, _)
  | P2.SARRAY (_, _, _, pr, _)
  | P2.ASSERT (_, pr, _)
  | P2.MAPS (_, _, pr, _)
  | P2.PARALLEL (_, _, pr, _)
  | P2.RETURN (_, pr, _)
  | P2.CONTINUE (pr, _)
  | P2.LABEL (_, pr, _) ->
     pr
  | P2.BREAK (pr, _) -> pr

let subs_func_pointer modules globals (sorted_functions : string list list) programs structures =

  (** Local declaration and initialization *)
  dbg "FPA" "Sorted Functions:" (iterS (fun ss -> iterS p "," ss) ";") sorted_functions;
  dbg "FPA" "Number of modules:" pl (List.length modules) ;

  let sorted_flat_functions = List.concat sorted_functions in

  let (mod_done : bool F.t) = (fun ms (n, _, _, _, _, _) -> F.add n false ms) |->> ((F.empty : bool F.t), modules) in

  let f_update l r m = F.add l r (F.remove l m) in
  let s_update l r m =
    let m' = try (S.remove l m) with _ -> pn "####ERROR####"; m in
    S.add l r m' in
(*
  (** ************** BEGIN process_a_function ************** *)
  let rec process_a_function (f_caller: string) ((s: s), (h: h)) r mod_done (args: Term.t list) (fn: string) =
    (** find the module where the requested function is contained *)
    try
      pn_s "FPA" (f_caller ^ " is going to be analyzed");
      let (f_module, _, _) =
        try
          F.find f_caller programs
        with
          _ -> raise ModuleNotFound
      in
      pn_s "FPA" ("Module is found: " ^ f_module);

      (** check if the globals are already processed *)
      let is_mod_done =
        try
          F.find f_module mod_done
        with
          _ -> raise (StError (f_module ^ " is not found in is_module_done"))
      in
      pn_s "FPA" (f_module ^ ".is_mod_done: " ^ (if is_mod_done then "true" else "false"));

      (** if global is not processed then process it and update global *)
      let (s',h') =
        if is_mod_done then
          ((s,h),r)
        else
          begin
            let ((s',h'),r') = execute_global (s,h) r f_module in
            pn_s "FPA" "Global execution is finished";
(*            dbg "FPA" "Global Postcondition (store):" print_all s';
            dbg "FPA" "Global Postcondition (spatial):" (iterS Pointer.pprint "*") h'; *)
            ((s',h'),r')
          end
      in

      let (is_module_done : bool F.t) = f_update f_module true mod_done in

      (** now proceed to the function *)
      pn_s "FPA" (fn ^ " is going to be called for analysis");
      let (_s'', spatial'') =
          execute_function (s',h') r args fn f_caller mod_done
      in
      pn_s "FPA" (fn ^ " is analyzed");
      (** return the result *)
      ((_s'', spatial''), is_module_done, [])
    with
      ModuleNotFound ->
      begin
        pn (fn ^ " is not found in programs. So, no module is loaded. Calling function is: " ^ f_caller);
        (((s, h),r), mod_done, [])
      end
*)
  (** ************** END process_a_function ************** *)
(*
  (** ************** BEGIN execute_global ************** *)
  and execute_global (s,h) r f_module =
    pn_s "FPA" (f_module ^ "'s globals are is going to be analyzed");

    let (progs, _, _, _) =
      try
        F.find f_module globals
      with
        _ -> raise (StError (f_module ^ " is not in globals"))
    in
    (** TODO: Change fst to snd after checking *)
    fst ((fun ((s,h),r) _p ->
      match _p with
        | Global.STATEMENT _p' ->
           funcp (s,h) r "" mod_done _p'
        | _ -> ((s,h),r)
    ) |->> (((s,h),r), progs))
  (** ************** END execute_global ************** *)
 *)
(*
  (** ************** BEGIN execute_function ************** *)
  and execute_function (s,h) r args fn f_caller mod_done =
    pn_s "FPA" (fn ^ " is in 'execute_function'");

    let dl = Locs.dummy in
    let take n ls = List.rev $$ fst ((fun (acc,i) x -> if i<n then (x::acc,i+1) else (acc,i)) |->> (([],0), ls)) in
    (** Get the function details: the parameters and the body *)
    let (_, _, (f_name, params, body)) =
      try
        F.find fn programs
      with
        _ -> raise (StError (fn ^ " is not found in programs in execute_function."))
    in

(*    (** Add/update function pointer parameters' associations to actual function names *)
    let add_param_fp (s,h) key (afs : (Term.t * string) list) =
      add_s fn (s,h) 0
    in *)

    let (s',h') =
      if List.length args = 0 then
        if List.length params = 0 then
          (** Natural, no parameters, and so proceed directly
              Or
              Starting function and so create dummy args that is same as params
           *)
          funcp (s,h) (S.empty, H.empty) fn mod_done body
        else
          (** We don't care if there are parameters but no arguments provided. It is unsafe and should be updated. (TODO) *)
          begin
            pn_s "FPA" ("No argument and so aborting: " ^ fn);
            (s,h)
          end
      else
        let params_args : (Var.t * Term.t) list =
          if List.length args = List.length params then
            let params' = Procedure.to_var |>>| params in
            List.combine params' args
          else
            let min = if List.length args > List.length params then List.length params else List.length args in
            let args' = take min args in
            let params' = Procedure.to_var |>>| (take min params) in
            List.combine params' args'
        in

        let body' = (fun b (p,a) ->
            P2.DECL (p,[],[],P2.ASSIGN (p,a,b,dl),dl)
          ) |->> (body, List.rev params_args) in

        let body'' = P2.BLOCK (body', P2.SKIP, dl) in

        let (s',h') = funcp (s,h) (S.empty, H.empty) fn mod_done body'' in
        (s',h')
    in
    (s',h')
 *)
(*
            let ((s',h'), _body') =
              (fun ((s,h), body) (p, a') ->
                let a'' =
                  match a' with
                  | Term.EXP (Exp.ADDR (v)) ->
                     Term.EXP v
                  | Term.EXP (Exp.VAR (v, attr)) when Bytes.get v 0 = '&' ->
                     let tt = (Bytes.sub v 1 (Bytes.length v - 1), attr) in
                     Term.EXP (Exp.VAR tt)
                  | _ -> a'
                in

                let a =
                  if not (Var.is_proto p) then
                    a''
                  else
                  match a'' with
                    Term.EXP (Exp.VAR v) ->
                    begin
                      let attr = Var.get_attributes v in
                      if Var.to_str v |<- sorted_flat_functions then
                        Term.encode v
                      else 
                        let rf =
                          if S.mem (calling_function, FuncPtr.FUNC_POINTER (a'')) s then
                            S.find (calling_function, FuncPtr.FUNC_POINTER (a'')) s
                          else if S.mem (calling_function, FuncPtr.VARIABLE (a')) s then
                            S.find (calling_function, FuncPtr.VARIABLE (a'')) s
                          else if S.mem ("", FuncPtr.VARIABLE (a'')) s then
                            S.find ("", FuncPtr.VARIABLE (a'')) s
                          else if S.mem (calling_function, FuncPtr.PARAM (calling_function, a'')) s then
                            S.find (calling_function, FuncPtr.PARAM (calling_function, a'')) s
                          else
                            begin
                              print_all s;
                              pn calling_function;
                              pn fn;
                              raise (NotFound ("Procedure Not Found " ^ (Term.toStr a')))
                            end
                        in

                        let rec get_proc_name rf =
                          match rf with
                            FNAME t -> Term.encode (t, attr)
                          | FNAMES ts -> Term.encode (snd (List.nth ts ((List.length ts) - 1)), attr)
                          | PVAR v ->
                             print_all s;
                             (* raise Error; *)
                             a''
                          | STRUCT_REF (v, f) -> get_proc_name (S.find (calling_function, FuncPtr.FIELD (v, f)) s)
                          | REF r -> get_proc_name (S.find r s)
                        in
                        get_proc_name rf
                    end
                  | _ -> raise (NotFound ("Procedure Name is Invalid " ^ (Term.toStr a')))
                in
                let (s', h, body') =
                  if Var.is_proto p then
                    let key = (fn, FuncPtr.PARAM (fn, Term.encode p)) in
                    let actual_function =
                      if S.mem (calling_function, FuncPtr.FUNC_POINTER a) s then
                        (** If the argument is a non-parameter function pointer, we need what is refers to *)
                        Some (S.find (calling_function, FuncPtr.FUNC_POINTER a) s)
                      else if S.mem (calling_function, FuncPtr.PARAM (calling_function, a)) s then
                        (** If the argument is itself a parameter *)
                        Some (S.find (calling_function, FuncPtr.PARAM (calling_function, a)) s)
                      else if (Term.toStr a) |<- sorted_flat_functions then
                        (** If the arguent is a real function *)
                        Some (FNAME (Term.toStr a))
                      else
                        (** Ordinary argument *)
                        None
                    in

                    (** get the actual name of functions the argument represents *)
                    let afs =
                      match actual_function with
                      | Some (FNAME af) -> [(a',af)]
                      | Some (FNAMES afs) -> afs
                      | _ -> []
                    in

                    (** add those new functions names to the parameter's current associated function names *)
                    let s' = add_param_fp s key afs in
                    (** substitute the body as well *)
                    let body' = Block.substitute (Term.encode p) a body in
                    (* S.iter (fun key value -> FuncPtr.pprint key; pn " -> "; pprint_s_t value; pn "") s'; *)
                    (s', h, body')
                  else
                    begin
                      let key = (fn, FuncPtr.VARIABLE (Term.encode p)) in
                      if Var.is_ptr p then
                        (** Use ref *)
                        let actual_value =
                          match a with
                            Term.EXP (Exp.ADDR x) -> REF (calling_function, FuncPtr.VARIABLE (Term.EXP x))
                          | Term.NULL -> PVAR (Term.NULL)
                          | _ -> REF (calling_function, FuncPtr.VARIABLE a)
                        in
                        let s' = S.add key actual_value s in
                        (s', h, body)
                      else
                        let actual_value =
                          try
                            PVAR (Term.map (lookup calling_function s) a)
                          with
                            e -> PVAR Term.NULL
                        in
                        let s' = S.add key actual_value s in
                        (s', h, body)
                    end
                in

                ((s', h), body')
              ) |->> (((s,h), body), params_args)
            in

            funcp (s',h') fn is_module_done _body'
          end
        else
          (s, h)
    in
    pn_s "FPA" (fn ^ " is done in funcp");
    (s',h')
 *)
(** *********************************************** *)

  let rec funcp counter ((s,h):s*h) (r:s*h) proc (mod_done: bool F.t) (prog : P2.t) : ((s*h) option * (s*h) * int) =

    let get_structure name =
      List.find (fun (nm,_) -> nm = name) structures
    in

    let rec var_size var : int =
      if Var.is_struct var then
        let sn = Var.get_struct_name var in
        let (_, fields) = get_structure sn in
        let field_size = (fun acc (fn,_) -> if Var.is_struct fn then acc + var_size fn else acc) |->> (0, fields) in
        field_size + 1
      else
        1
    in

    let foreach f acc (s,n) =
      let rec aux f acc i =
        if i <= n then
          aux f (f acc i) (i+1)
        else
          acc
      in
      aux f acc s
    in

    let rec _AllocTypeFP (h:h) (k:int) (var:Var.t) (n:int) : h =
      if Var.is_struct var then
        let sn = Var.get_struct_name var in
        let (_, fields) = get_structure sn in
        let t_fields, s_fields = List.partition (fun (fld, _) -> Var.is_struct fld && not (Var.is_ptr fld)) fields in
        let f1 (h:h) (i:int) : h =
          let h',_,_ = (fun (h, k_i_1, sz) (fld,_) ->
              let k_i = k_i_1 + sz in
              let h'' = H.add (_C k, fst fld) (INTV (_C k_i, _C k_i)) h in
              let sz_i = var_size fld in
              let h''' = _AllocTypeFP h'' k_i fld sz_i in
              (h''', k_i, sz_i)
            ) |->> ((h, k, 0), t_fields) in
          (fun h (fld,_) -> H.add (_C k, fst fld) (INTV (E.UNDEF, E.UNDEF)) h) |->> (h', s_fields)
        in
        foreach f1 h (k, k+n-1)
      else
        foreach (fun (h:h) (x_i:int) ->
            let key : Loc.t = (_C x_i, "*") in
            let h':h = H.add key (INTV (E.UNDEF, E.UNDEF)) h in
            h'
          ) h (k, k+n-1)

(*
      let _x_n = _x @+ _n in
      (*  ("Array", [_x; _x_n @-@ (_T (_C 1))]) *)
      match _n with
        (Exp.CONST _c) ->
        begin
          let sn = Var.get_struct_name var in
          let (_, fields) = get_structure sn in
          let fields' = (fun (fld, _) -> Var.is_struct fld && not (Var.is_ptr fld)) |>- fields in
          if List.length fields' = 0 then
            []
          else
            let _k = (fun acc (fld,_) -> acc + var_size fld) |->> (0, fields') in
            let rec aux j u d =
              if j <= u then
                let _kj1 = _x_n @+ (_C ((j-1)*_k)) in
                let field1 = List.hd fields' in
                let fld1 = fst field1 in
                let one = (_C 1) in
                let alloctype_1 = _AllocTypeFP _kj1 fld1 one in

                let fields'', allocs, _, _ =
                  (fun (acc1, acc2, fldi_1, _kji_1) ((fldi : Var.t), _) ->
                    let fldi_1_size : int = var_size fldi_1 in
                    let _kji = _kji_1 @- (_C fldi_1_size) in
                    let alloctype_i = _AllocTypeFP _kji fldi one in
                    (acc1 @ [(Var.to_str fldi, _kji)], acc2 @ alloctype_i, fldi, _kji)
                  ) |->> (([(Var.to_str fld1, _kj1)], alloctype_1, fld1, _kj1), List.tl fields') (** i in 1 to l *)
                in

                let _x_j = _x @+ (_C j) in
                let cell = (_x_j, fields'') in
                d @ (cell :: allocs)
              else
                d
            in
            let r1 = aux 1 _c [] in
            r1
        end
      | _ -> []
 *)
    in

    match prog with
      | P2.SKIP ->
         pn_s "FPA" ("Done.");
         Some (s,h),r,counter
      | P2.ASSIGN (x, t, _, _) ->
         let t':t = eval_t (s,h) t in
         let s':s = set_var x t' s in
         Some (s',h),r,counter
      | P2.IF (b, p1, p2, pr, _) ->
         let xs = BExp.fv b in
         let s_xs = (fun x -> (x, eval_var s x)) |>>| xs in
         let intvs = (fun (x, intv) ->
             match intv with
               INTV (a,b) -> enumerate x a b
             | FUNS fs -> false, []
           ) |>>| s_xs in
         let intvs' = fst |>- intvs in
         let combs = all_combs (snd |>>| intvs') in
         let bb =
             (fun xs ->
               let s' =
                 (fun s (x,a) ->
                   let s' = set_var x (INTV (a, a)) s in
                   s'
                 ) |->> (s, xs) in
               eval_b (s',h) b
             ) |>>| combs in
         if List.for_all (fun o ->
                match o with
                  Some b -> b
                | None -> false) bb then
           funcp counter (s,h) r proc mod_done p1
         else if List.for_all (fun o ->
                match o with
                  Some b -> not b
                | None -> false) bb then
           funcp counter (s,h) r proc mod_done p2
         else
           begin
             let (or1,r1',counter') = funcp counter (s,h) r proc mod_done p1 in
             let (or2,r2',counter'') = funcp counter' (s,h) r proc mod_done p2 in
             match or1,or2 with
               Some r1, Some r2 ->
               (Some (r_union r1 r2), r_union r1' r2', counter'')
             | None, _ ->
                (or2, r_union r1' r2', counter'')
             | _, _ ->
                (or1, r_union r1' r2', counter'')
           end
      | P2.RETURN (t, _, _) ->
         let t' = eval_t (s,h) t in
         let s' = set_var ret t' s in
         (None, (s',h), counter)
      | P2.WHILE (b, block, _, _, _) ->
         let (or1,r2,counter') = funcp counter (s,h) r proc mod_done block in
         let rec aux i acc = if i <= counter' then aux (i+1) (i::acc) else acc in
         let inner_calls = aux (counter+1) [] in
         let s' = 
           match or1 with
             Some (s1,_) ->
             (fun s i ->
               let fns = get_funs s1 proc i in
               add_fn_s s proc i fns
             ) |->> (s, inner_calls)
           | None -> s
         in
         (Some (s',h),r,counter')
      | P2.MALLOC (x, t, _, _, _) ->
         let k =
           try
             begin
               match fst (fst $$ H.max_binding h) with
                 E.CONST c -> c + 1
               | _ -> 0
             end
           with
             _ -> 0
         in
         let s' = set_var x (INTV (_C k,_C k)) s in
         if Var.is_struct x then
           let t' = eval_t (s,h) t in
           let h' =
             match t' with
               INTV (l, E.CONST n) ->
               _AllocTypeFP h k x n
             | _ -> h
           in
           Some (s',h'),r, counter
         else
           Some (s',h),r, counter

      | _ -> Some (s,h),r, counter
  in
  (***)
(*
  let rec subs_fp_in_body s (proc_name, attrs) params = function
      [] -> []
    | _ -> []
  in
 *)

(*
  let subs_fp_in_proc _s mod_name ((proc_name, attr), params, body) : Procedure.t =
    let proc_name' = get_unique_func proc_name mod_name in
    ((proc_name,attr), params, subs_fp_in_body _s (proc_name',attr) params body)
  in

  let subs_fp_in_global _s mod_name = function
      Global.PROC (proc, p, q, r, s) -> Global.PROC (subs_fp_in_proc _s mod_name proc, p, q, r, s)
    | x -> x
  in

  let subs_fp_in_modules _s (name, fpath, l_globals, p, q, r) =
    (name, fpath, (subs_fp_in_global _s name) |>>| l_globals, p, q, r )
  in

  
  let modules' = (subs_fp_in_modules _s) |>>| modules in
  pn_s "FPA" "**********************************";
  pf_s "FPA" (iterS (fun (_, _, l_globals, _, _, _) -> iterS Global.pprint "\n" l_globals) "\n\n") modules;
  pn_s "FPA" "**********************************";
  pf_s "FPA" (iterS (fun (_, _, l_globals, _, _, _) -> iterS Global.pprint "\n" l_globals) "\n\n") modules';
  modules'
 *)
  []
