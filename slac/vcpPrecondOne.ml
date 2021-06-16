open Ftools
open VcpBase
open VcpTranslate

type t =
    | SKIP
    | ASSIGN of Var.t * Term.t * Locs.t
    | IF of BExp.t * t * t * Locs.t
    | CONS of Exp.t * (string * Term.t) list * Locs.t  (** Name, fields, rest *)
    | MUTATION of Term.t * Field.t * Term.t * Locs.t
    | LOOKUP of Var.t * Term.t * Field.t * Locs.t
    | DISPOSE of Term.t * Locs.t
    | COMP of t * t * Locs.t
    | ARRAY of Var.t * Term.t * Term.t list * Locs.t (** Name, Length, rest *)
;;

let rec toT = function
    | Block.SKIP ->
       SKIP
    | Block.ASSIGN (var, exp, pr, l) ->
       COMP (ASSIGN (var, exp, l), toT pr, l)
    | Block.IF (b, p1, p2, pr, l) ->
       COMP (IF (b, toT p1, toT p2, l), toT pr, l)
    | Block.WHILE (b, block, inv, pr, l) ->
       toT pr
    | Block.CONS (exp, fields, pr, l) ->
       COMP (CONS (exp, fields, l), toT pr, l)
    | Block.MUTATION (obj, fieldname, to_assign, pr, l) ->
       COMP (MUTATION (obj, fieldname, to_assign, l), toT pr, l)
    | Block.LOOKUP (var, obj, fieldname, pr, l) ->
       COMP (LOOKUP (var, obj, fieldname, l), toT pr, l)
    | Block.DISPOSE (obj, pr, l) ->
       COMP (DISPOSE (obj, l), toT pr, l)
    | Block.PROCCALL (a, b, c, d) -> 
       p "Procedure call is skipped: "; pn a;
       toT c 
    | Block.ARRAY (a,b,c,d,l) ->
       COMP (ARRAY(a,b,c,l), toT d, l)
    | x ->
       Block.pprint 0 x;
       raise (StError "Program conversion error")

    

let rec intersection xs = function
    [] -> []
  | (y::ys) -> 
     if y |<- xs then 
       y::intersection xs ys 
     else 
       intersection xs ys

let sepconj (formula : Formula.t) (exs, pointers) : Formula.t =
  let fvp = Var.toStr |>>| (List.concat (Pointer.fvs |>>| pointers)) in
  (fun (a,b,c,d) -> if List.for_all (fun a -> not (a |<- fvp)) a then (a @@ exs, b, c @ pointers, d) else (a,b,c,d)) |>>| formula



let rec split3 = function
    []           -> [], [], []
  | ((a,b,c)::xs) -> let (ax, bx, cx) = split3 xs in (a::ax, b::bx, c::cx)

let fst3 (x, _, _) = x

let snd3 (_, x, _) = x

let trd3 (_, _, x) = x

let field_concat fields1 fields2 =
  if fields1 = [] then
    fields2
  else if fields2 = [] then
    fields1
  else
    let fns1 = fst |>>| fields1 in
    let fields2' = List.filter (fun (fn, fd) -> not (fn |<- fns1)) fields2 in
    fields1 @ fields2'

let pointer_merge (p1, fields1) (p2, fields2) =
  if Term.toStr p1 = Term.toStr p2 then
    begin

      [(p1, field_concat fields1 fields2)]
    end
  else
    [(p1, fields1); (p2, fields2)]

let pointer_concat (pointers1:string list * Pointer.t list) (pointers2: string list * Pointer.t list) : string list * Pointer.t list =
  if snd pointers1 = [] then
    pointers2
  else if snd pointers2 = [] then
    pointers1
  else
    let rec aux ((p, fs):Pointer.t) (aa:Pointer.t list) =
      match aa with
        [] -> [(p, fs)]
      | ((pa, fsa)::a) -> 
         if p = pa then
           (pa, field_concat fs fsa) :: a
         else
           (pa, fsa)::aux (p, fs) a
    in
      (fun ((exs, a)) p -> (exs @@ fst pointers2, aux p a)) |->> (pointers1, snd pointers2)

let rec getMissingCells precondition (program : t) : Formula.t * (string list * Pointer.t list) * Var.t list = 
  (* prerr_int (List.length precondition); prerr_newline (); *)
  let res      = (fun x -> getMissingCells2 x program) |>>| precondition in
  let cs       = split3 res in
  let pointers = (fun a c -> pointer_concat c a) |->> (([],[]), snd3 cs) in
  let p_fvs    = (fun a c -> c @@ a) |->> ([], Pointer.fvs |>>| (snd pointers)) in
  let i_mvs    = (fun a c -> c @@ a) |->> ([], trd3 cs) in
  (* p "fv(c1,c2,...): "; iterS Var.pprint "," p_fvs; pn "";
    p "mod(P): "; iterS Var.pprint "," i_mvs; pn ""; *)
  let cm = common p_fvs i_mvs in
  (* let fill spatial = 
    let ptrs = fst |>>| spatil in
    let missed = (fun (p,_) -> not (p |<- ptrs)) |>- pointers in
    spatial @ 
  in *)
  (* p "common: "; iterS Var.pprint "," cm; pn ""; *)
  let post = List.concat (fst3 cs) in
  let post = (fun (a,b,c,d) -> let c' = snd (pointer_concat ([],c) pointers) in (a,b,c',d)) |>>| post in
  (* Formula.pprint post; pn ""; *)
  if cm = []  then
    post, pointers, List.concat (trd3 cs)
  else
    [], ([], []), List.concat (trd3 cs)
      
(** Handles existential quantifiers *)
and getMissingCells2 ((exs, pures, pointers, preds) : (string list * BExp.t list * Pointer.t list * Predicate.t list)) program : Formula.t * (string list * Pointer.t list) * Var.t list =
  let ((postcondition : Formula.t), (exs1, missingCells), modvs) = getMissingCells1 ([], pures, pointers, preds) program in
  let p_fvs = (Var.toStr |>>| (List.concat (Pointer.fvs |>>| missingCells))) in
  let p_fvs, _ = drop_common p_fvs exs1 in
  (* p "Ex: "; iterS p "," exs; p " and ";
  p "fv(C): "; iterS p "," p_fvs; pn ""; *)
  (* p "POST: "; Formula.pprint postcondition; *)
  let rec drop_ex exs = function
      [] -> exs, []
    | ((a,b,c,d)::posts) ->
       let (a', exs') = drop_common a exs in
       let exs'', posts' = drop_ex exs' posts in
       exs'', (a',b,c,d)::posts'
  in
  let exs1, postcondition = drop_ex exs1 postcondition in
  if common exs p_fvs = [] then
    let post = (fun (a,b,c,d) -> (a @@ exs, b, c, d)) |>>| postcondition in
    (post, (exs1, missingCells), modvs)
  else
    begin
      pn "Proof breaks at Precond2";
      ([], ([],[]), modvs) 
      (* raise (StError "Stuck at Precond2") *)
    end


and getMissingCells1 (prec : (string list * BExp.t list * Pointer.t list * Predicate.t list)) (program : t) : Formula.t * (string list * Pointer.t list) * Var.t list =
  
match program with
  | SKIP            ->
     [prec], ([], []), []
  | ASSIGN (var, exp, l) ->
     let fv'  = VcpVBase.newvar () in
     let exp' = VcpVBase.term_subs exp var fv' in
     let pre': Formula.t = VcpVBase.formula_subs [prec] var fv' l in
     let post = VcpVBase.ex fv' (VcpVBase.conjunct pre' (VcpVBase.eq var exp')) in
     (post, ([], []), Var.fv var)
  | IF (b, p1, p2, l) ->
    (* prerr_endline "IF"; prerr_endline (Locs.toStr l); *)
     let preb = List.hd (VcpVBase.conjunct [prec] b) in
     let prenb = List.hd (VcpVBase.neg_conjunct b [prec]) in
     (* pw "CHECK SAT";
     pn (Locs.toStr l); 
     Formula.pprint [preb]; pn ""; *)
     pn (Locs.toStr l); 
     let isp1 = VcpVBase.check_sat true preb in
     (* pn "IF-Pos is finished"; pn (Locs.toStr l); *)
     let isp2 = 
       if not isp1 then
         true
       else
         begin
           (* Formula.pprint [prenb]; pn ""; *)
           pn (Locs.toStr l); 
           let isp2' = VcpVBase.check_sat true prenb in
           (* pn "IF-Neg is finished"; pn (Locs.toStr l); *)
           isp2'
         end
     in
     let (d1, c1, m1) =
       if isp1 then
         getMissingCells1 preb p1
       else
         ([], ([], []), [])
     in
     (* prerr_endline "IF-P1 is done"; prerr_endline (Locs.toStr l); *)
(*     pw "d1:"; Formula.pprint d1; pn ""; *)
     let (d2, c2, m2) = 
       if isp2 then
         getMissingCells1 prenb p2
       else
         ([], ([], []), [])
     in 
     (* prerr_endline "IF-P2 is done"; prerr_endline (Locs.toStr l); *)
(*     pw "d2:"; Formula.pprint d2; pn ""; *)
     let (d', c') =
       if intersection (List.concat (Pointer.fvs |>>| (snd c2))) m1 = [] && intersection (List.concat (Pointer.fvs |>>| (snd c1))) m2 = [] then
         begin
(*           Formula.pprint [prec]; pn "";
           iterS Pointer.pprint "*" c2; pn " --1";
           Formula.pprint d1; pn " --2";
           iterS Pointer.pprint "*" c1; pn " --3";
           Formula.pprint d2; pn " --4"; *)
           let post = 
         (*    if not isp1 then
               sepconj d2 c1
             else if not isp2 then
               sepconj d1 c2
             else *)
               (sepconj d1 c2) @ (sepconj d2 c1) in
(*           Formula.pprint post; pn " --5"; *)
           post, pointer_concat c1 c2
         end
       else
(*         begin
           prerr_endline ("Proof breaks at IF at " ^ Locs.toStr l);
           let post = (sepconj d1 c2) @ (sepconj d2 c1) in
           post, pointer_concat c1 c2
         end *)
         raise (StError "IF problem")
     in
     (d', c', m1 @@ m2)
  | COMP (p1, p2, l) ->
     (* pn (Locs.toStr l);
     Formula.pprint [prec]; pn ";;"; *)
     let (d1, c1, m1) = getMissingCells1 prec p1 in
     (* pw (Locs.toLine l); pw "d1:";
     Formula.pprint d1; pw " c1:"; iterS Pointer.pprint "*" c1; pn ""; *)
     let (d, (c2:string list * Pointer.t list), m2) = getMissingCells d1 p2 in
     (* pw (Locs.toLine l); pw "d:";
     Formula.pprint d; pw " c2:"; iterS Pointer.pprint "*" c2; pn ""; *)
     let p_fvs = List.concat (Pointer.fvs |>>| (snd c2)) in
     let i_fvs = intersection p_fvs m1 in
(*     pw "RET: "; Formula.pprint d; pn ""; *)
     if i_fvs = [] then
       (d, pointer_concat c1 c2, m1 @ m2)
     else
       begin         
         pn ("Proof breaks at COMP at " ^ Locs.toStr l);
         pw "MOD(P1)"; iterS Var.pprint "," m1; pn "";
         pw "FV(C2)"; iterS Var.pprint "," p_fvs; pn "";
         ([], ([],[]), [])
(*
         raise (StError "Stuck at Composition") *)
(*         pw "fv(c2)="; iterS Var.pprint "," p_fvs; pw ""; pw "mod(p1)="; iterS Var.pprint "," m1; pn "";
         (d, c1 @ c2, m1 @ m2) *)
       end
  | CONS (exp, fields, loc) ->
     let fv'  = VcpVBase.newvar () in
     let var  =
       match exp with
         Exp.VAR v -> v
       | Exp.BINOP (Exp.VAR v, _, _) -> v
       | _ -> raise SError
     in
     let pre': Formula.t = VcpVBase.formula_subs [prec] var fv' loc in (** A' *)
     let post1 = VcpVBase.ex fv' (sepconj pre' ([], [(Term.EXP exp, fields)])) in
     let post2 = 
       if Var.is_ptr var && not (Var.is_array var) then
         VcpVBase.ex fv' (VcpVBase.conjunct pre' (VcpVBase.eq var Term.NULL))
       else 
         []
     in
     (post1 @ post2, ([], []), Var.fv var)
  | ARRAY (a,b,c,l) ->
     begin
         match b with
           Term.EXP (Exp.INDICES (Exp.CONST m::_)) ->
           let rec iter n css ptrs =
             let value,rest = match css with [] -> Term.EXP Exp.NOTHING,[] | (c::cs) -> c, cs in
             let ptr : Pointer.t = (Term.EXP (Exp.BINOP (Exp.VAR a, Op.ADD, Exp.CONST n)), [("*", value)]) in
             if n = m then
               ptrs
             else
               iter (n+1) rest (ptrs @ [ptr])
           in
           let prec' = sepconj [prec] ([], iter 0 c []) in
           prec', ([], []), []
         | _ -> [prec], ([],[]), []
       end
  | MUTATION (obj, fieldname, to_assign, loc) -> 
     begin
       let (a, b, c, d) = prec in
       let cells, others = List.partition (fun (ptr, _) -> Formula.(===) b ptr obj) c in
       match cells with
         [] ->
         let x' = VcpVBase.newvar () in
         let x = Term.encode x' in
         let post = VcpVBase.ex x' (sepconj [prec] ([],[(obj,[(fieldname, to_assign)])])) in
         (post, ([Var.toStr x'], [(obj, [(fieldname, x)])]), [])
       | [(ptr, fields)] ->
          let fields' = 
            if (fieldname |<-  (fst |>>| fields)) then
              (fun (f, v) -> if f = fieldname then (f, to_assign) else (f, v)) |>>| fields 
            else
              fields @ [(fieldname, to_assign)]
          in
          let cell : Pointer.t = (ptr, fields') in
          [(a, b, cell::others, d)], ([],[]), []
       | _ ->
          [([], [], [], [("Dual Existence",[])])], ([],[]), []
     end
  | LOOKUP (x, p, fieldname, loc) ->
     begin
       let (a, b, c, d) = prec in
       (** Matching cells, Unmatching cells *)
       let cells, others = List.partition (fun (ptr, _) -> Formula.(===) b ptr p) c in
       (** Existensial quantifier *)
       let x' = VcpVBase.newvar () in 
       let p' = Term.substitute (Term.encode x) (Term.encode x') p in
       let pre' = VcpVBase.formula_subs [(a, b, c, d)] x x' loc in
       (** Fresh variables *)
       let y = Term.encode (VcpVBase.newvar ()) in
       match cells with
         [] ->
         let post' = VcpVBase.ex x' (sepconj (VcpVBase.conjunct pre' (VcpVBase.eq x y)) ([], [(p', [(fieldname, y)])])) in
         let post  = VcpVBase.ex (Term.decode y) post' in
         (post, ([Term.toStr y], [(p, [(fieldname, y)])]), Var.fv x)
       | [(ptr, fields)] ->
          begin
            let field = List.filter (fun (fn, fd) -> fn = fieldname) fields in
            match field with
              [(_, fdata)] ->
              begin
                let t' = VcpVBase.term_subs fdata x x' in
                let post = VcpVBase.ex x' (VcpVBase.conjunct pre' (VcpVBase.eq x t')) in
                try
                  post, ([],[]), Var.fv x
                with
                  _ -> raise Error
              end
            | _ ->
               begin
                 try
                   let (a,b,c,d) = List.hd (VcpVBase.ex x' (VcpVBase.conjunct pre' (VcpVBase.eq x y))) in
                   [(a,b,others @ [(ptr, fields @ [(fieldname, y)])], d)], ([Term.toStr y],[(p, [(fieldname, y)])]), Var.fv x
                 with
                   _ -> raise Error
               end
(*               let (a,b,c,d) = pre' in
               let post = (a,b, others @ [(ptr, fields @ [(fieldname, y)])] ,d) in
               [], ([],[]), Var.fv x *)
          end
       | _ ->
          [(a, b, c, [("Dual Existence",[])])], ([],[]), Var.fv x
     end
  | DISPOSE (obj, loc) ->
     begin
     let (a, b, c, d) = prec in
     let cells, others = List.partition (fun (ptr, _) -> Formula.(===) b ptr obj) c in
     match cells with
       [] ->
       let t' = Term.encode (VcpVBase.newvar ()) in
       [prec], ([Term.toStr t'], [(obj, [("...", t')])]), []
     | [_] ->
        let post = [(a, b, others, d)] in
        post, ([],[]), []
     | _ ->
        [(a, b, c, [("Dual Existence",[])])], ([],[]), []
       end
(*
let rec cutoff program = 
  match program with
    CONS (var, _, l) -> program, [Term.EXP var]
  | LOOKUP (_, ptr, _, l) -> program, [ptr]
  | MUTATION (ptr, _, _, _) -> program, [ptr]
  | COMP (p1, p2, _) ->
     let (_, v2) = cutoff p2 in
    if v2 = [] then
      p1, []
    else
      program, v2
  | _ -> program, []
 *)


let get_dependency_0 name body =
  let rec aux previous = function
    | Block.SKIP ->
       []
    | Block.ASSIGN (var, exp, pr, l) ->
       aux previous pr
    | Block.IF (b, p1, p2, pr, l) ->
       aux previous p1 @@ aux previous p2 @@  aux previous pr
    | Block.WHILE (b, block, inv, pr, l) ->
       aux previous block @@ aux previous pr
    | Block.CONS (exp, fields, pr, l) ->
       aux previous pr
    | Block.MUTATION (obj, fieldname, to_assign, pr, l) ->
       aux previous pr
    | Block.LOOKUP (var, obj, fieldname, pr, l) ->
       aux previous pr
    | Block.DISPOSE (obj, pr, l) ->
       aux previous pr
    | Block.PROCCALL (a, b, c, d) -> 
       a::aux previous c
    | Block.ARRAY (a,b,c,d,l) ->
       aux previous d
    | x ->
       Block.pprint 0 x;
       raise (StError "Unsupported program")
  in
  aux [name] body

