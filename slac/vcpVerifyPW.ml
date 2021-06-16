open VcpBase
open VcpTranslate
open Ftools
open VcpVBase


let simp formula = formula


let norm formula = Formula.fpurify formula


(** Interval logic +++++++++++++++++++++++++++++++++++++++++++++++ *)

(**
                  x in [a, b]          == a-1 < x & x < b+1
   x <= t      == x in [a, min(b,t)]   == a-1 < x & x < min(b,t)+1
   x /= t      == x in [a, b]          == a-1 < x & x < b+1

   x in [a1, b1] OR  x in [a2,b2]       == x in [min(a1,a2), max(b1,b2)]
   x in [a1, b1] AND x in [a2,b2]       == x in [max(a1,a2), min(b1,b2)]

   WIDENING:
   L & x in [a,b] NABLA A --> x in [a, +inf] if L & A -> a-1 < x
   L & x in [a,b] NABLA A --> x in [-inf, b] if L & A -> x < b+1
                          --> x in [-inf,+inf] otherwise
   [-inf,b] are similar

   EQUIVALENCE:
   x in [a, a]           == x = a
   x in [-inf, +inf]     == Ex t.x = t
   x in [-inf, a]        == x < a + 1
   x in [a, +inf]        == a-1 < x
   x in [a, b]           == a-1 < x & x < b+1

   WIDENING OF FORMULA:
   x = a AND x < b       == x in [a,a] AND x in [-inf,b-1]
 *)


(** F, x<-[l,u] ==> F & l-1<x & x<u+1 *)
let formula_of_intv formula intv =
  let convert formula (x, (l, u)) =
    let l1 = Exp.BINOP (l, Op.SUB, Exp.CONST 1) in
    let u1 = Exp.BINOP (u, Op.ADD, Exp.CONST 1) in
    let left = BExp.UNIT (Term.EXP l1, Op.LE, Term.EXP (Exp.VAR x)) in
    let right = BExp.UNIT (Term.EXP (Exp.VAR x), Op.LE, Term.EXP u1) in
    let f1 = conjunct formula right in
    conjunct f1 left
  in
  List.fold_left convert formula intv

(** Widening defined in page 9. *)
let nabla (b : Formula.t) e e1 ys =
  let b':Formula.t = formula_of_intv b e1 in
  (fun (x, (l,u)) ->
    (** l <= x *)
    let y1 = [([], [BExp.UNIT (Term.EXP l, Op.LE, Term.encode x)], [], []); ([], [BExp.UNIT (Term.EXP l, Op.EQ, Term.encode x)], [], [])] in
    (** x <= u *)
    let y2 = [([], [BExp.UNIT (Term.encode x, Op.LE, Term.EXP u)], [], []); ([], [BExp.UNIT (Term.encode x, Op.EQ, Term.EXP u)], [], [])] in
    let r1 = entail "NABLA" [b'] [y1] in
    let r2 = entail "NABLA" [b'] [y2] in
    if r1 && r2 then
      (x, (l,u))
    else if r1 then
      (x, (l, Exp.POSINF))
    else if r2 then
      (x, (Exp.NEGINF, u))
    else
      (x, (Exp.NEGINF, Exp.POSINF))
  ) |>>| e


let rec intv_or e1 = function
  [] -> e1
| (x, (l0,u0))::xs ->
  match List.partition (fun (y, _) -> y = x) e1 with
    [(_, (l1, u1))], xs' ->
    let l = Exp.min l0 l1 in
    let u = Exp.max u0 u1 in
    (x, (l,u)) :: intv_or xs' xs
  | _, xs' ->
     (** CONFUSION: is it "(x, (l0,u0))::intv_or xs' xs"? *)
     intv_or xs' xs (** if matched zero times since more than one times matching is unlikely. *)

let rec verify_symb_intv intv program ys =
    begin
      match program with
    | Block.SKIP -> intv
    | Block.ASSIGN (var, exp, program, l) ->
       let intv' = Var.update_interval intv var (Term.get_interval intv ys exp) in
       verify_symb_intv intv' program ys
    | Block.IF (b, p1, p2, pr, l) ->
       let eb = BExp.get_intervals intv ys b in
       let enb = BExp.get_intervals intv ys (BExp.complement b) in
       let post1 = verify_symb_intv eb p1 ys in
       let post2 = verify_symb_intv enb p2 ys in
       let ior = intv_or post1 post2 in
       verify_symb_intv ior pr ys
    | Block.WHILE (b, block, inv, body, l) ->
       begin
         verify_symb_intv intv body ys
       end
    | Block.CONS (exp, fields, pr, loc) ->
       verify_symb_intv intv pr ys
    | Block.MUTATION (obj, fieldname, to_assign, pr, loc) ->
       verify_symb_intv intv pr ys
    | Block.LOOKUP (var, obj, fieldname, pr, loc) ->
       verify_symb_intv intv pr ys
    | Block.DISPOSE (obj, pr, loc) ->
       verify_symb_intv intv pr ys
    | _ -> intv
    end

let rec bexps_to_pairs xs = function
    [] -> []
  | x::xss ->
     begin
       match x with
         BExp.UNIT (a, Op.EQ, b) when (a |<- xs) ->
         (a, b) :: (bexps_to_pairs xs xss)
       | BExp.UNIT (b, Op.EQ, a) when (a |<- xs) ->
          (b, a) :: bexps_to_pairs xs xss
       | _ -> bexps_to_pairs xs xss
     end;;

let rec get_E_t pairs xs t =
  if t |<- xs then
    snd (List.find (fun (x, t') -> x = t) pairs)
  else
    begin
      let t' = (fun t x -> 
                let e_x = get_E_t pairs xs x in
                Term.substitute x e_x t
        ) |->> (t, xs) in
      t'
end

let rec verify_loop_counter (pairs : (Term.t * Term.t) list) program ys xs =
    begin
      match program with
    | Block.SKIP -> pairs
    | Block.ASSIGN (var, exp, pr, l) ->
       let pairs' = (fun (x, t) -> if Term.decode x = var then (x, get_E_t pairs xs exp) else (x, t)) |>>| pairs in
       verify_loop_counter pairs' pr ys xs 
    | Block.IF (b, p1, p2, pr, l) ->
       verify_loop_counter pairs pr ys xs
    | Block.WHILE (b, block, inv, body, l) ->
       begin
       verify_loop_counter pairs body ys xs
       end
    | Block.CONS (exp, fields, pr, loc) ->
       verify_loop_counter pairs pr ys xs
    | Block.MUTATION (obj, fieldname, to_assign, pr, loc) ->
       verify_loop_counter pairs pr ys xs
    | Block.LOOKUP (var, obj, fieldname, pr, loc) ->
       verify_loop_counter pairs pr ys xs
    | Block.DISPOSE (obj, pr, loc) ->
       verify_loop_counter pairs pr ys xs 
    | _ -> pairs
    end


let rec verify ((pre, program) : Formula.t * Block.t) ((modules_a, vars, structures, procs, ys) as packs) : (Formula.t * Formula.t) list =
    begin
      rprint pre program;
      match program with
    | Block.SKIP -> [(pre, Formula.trueempty)]
    | Block.ASSIGN (var, exp, program, l) ->
       let fv'  = newvar () in
       let exp' = term_subs exp var fv' in
       let pre': Formula.t = formula_subs pre var fv' l in
       let conj = ex fv' (conjunct pre' (eq var exp')) in
       let post = norm conj in
  (*     let intv' = Var.update_interval intv var (Term.get_interval intv ys exp) in *)
       verify (post, program) packs
    | Block.IF (b, p1, p2, pr, l) ->
       let post1 = List.hd (verify (simp (conjunct pre b), p1) packs) in
       let post2 = List.hd (verify (simp (neg_conjunct b pre), p2) packs) in
       verify (disjunct (fst post1) (fst post2), pr) packs
    | Block.WHILE (b, block, inv, body, l) ->
       begin (*
       match b with
         BExp.UNIT (Term.EXP (Exp.VAR i), Op.LE, Term.EXP len) ->
         let firstrun = Block.IF (b, block, Block.SKIP, Block.SKIP, l) in
         let firstres = fst (List.hd (verify (pre, firstrun) packs)) in
         let secondrun = Block.ASSIGN (i, Term.EXP(Exp.BINOP(len, Op.SUB, Exp.CONST 1)), block, l) in
         let secondres = fst (List.hd (verify (Formula.empty, secondrun) packs)) in
         let pre' = disjunct firstres secondres in
         let postrun = Block.ASSIGN (i, Term.EXP len, body, l) in
         verify (pre', postrun) packs
       | _ -> *)
          let post = verify_while pre b block l packs in
          verify (post, body) packs
       end
    | Block.CONS (exp, fields, pr, loc) ->
       let fv'  = newvar () in
       let var  =
        match exp with
          Exp.VAR v -> v
        | Exp.BINOP(Exp.VAR v, _, _) -> v
        | _ -> raise SError
       in
       let pre': Formula.t = formula_subs pre var fv' loc in
       let post = norm (ex fv' (sep_conjunct (Term.EXP exp, fields) pre')) in
       verify (post, pr) packs
    | Block.MUTATION (obj, fieldname, to_assign, pr, loc) ->
       let post = (fun (a, b, c, d) ->
             let cells, others = List.partition (fun (ptr, _) -> Formula.(===) b ptr obj) c in
             match cells with
               [] ->
               ([], [], [], [("Abort", [])])
             | [(ptr, fields)] ->
                let _, um_fields = List.partition (fun (fn, fd) -> fn = fieldname) fields in
                let m_field = (fieldname, to_assign) in
                let cell : Pointer.t = (ptr, m_field::um_fields) in
                (a, b, cell::others, d)
             | _ ->
                ([], [], [], [("Dual Existence",[])])
         ) |>>| pre in
       verify (post, pr) packs
    | Block.LOOKUP (var, obj, fieldname, pr, loc) ->
       let post = (fun (a, b, c, d) ->
           let cells, others = List.partition (fun (ptr, _) -> Formula.(===) b ptr obj) c in
           match cells with
             [] ->
             ([], [], [], [("Abort", [])])
           | [(ptr, fields)] ->
              begin
                let field, _ = List.partition (fun (fn, fd) -> fn = fieldname) fields in
                match field with
                  [(fn, fdata)] ->
                  begin
                    let fv'  = newvar () in
                    let exp' = term_subs fdata var fv' in
                    let pre' = formula_subs [(a, b, c, d)] var fv' loc in
                    let post = norm (ex fv' (conjunct pre' (eq var exp'))) in
                    try
                      List.hd post
                    with
                      _ -> raise Error
                  end
                | _ -> (a, b, c, [("Missing Field", [])])
              end
           | _ ->
              (a, b, c, [("Dual Existence",[])])
         ) |>>| pre in
       verify (post, pr) packs
    | Block.DISPOSE (obj, pr, loc) ->
       let post = (fun (a, b, c, d) ->
           let cells, others = List.partition (fun (ptr, _) -> Formula.(===) b ptr obj) c in
           match cells with
             [] ->
             ([], [], [], [("Abort", [])])
           | [_] ->
              let post = norm [(a, b, others, d)] in
              List.hd post
           | _ ->
              (a, b, c, [("Dual Existence",[])])
         ) |>>| pre in
       verify (post, pr) packs
(*    | Block.ARRAY (a, b, tl, body, _) ->
      let pre' =
        if tl = [] then
          let array_pred = ("Array", [Term.encode a; b]) in
          (fun (exqs, eqs, c, pred) -> (exqs, eqs, c, array_pred::pred)) |>>| pre
        else
          (fun (exqs, eqs, c, pred) ->
             let pointers = List.mapi (fun i x -> (Term.EXP (Exp.BINOP (Exp.VAR a, Op.ADD, Exp.CONST i)), [("*", x)]) ) tl in
             (exqs, eqs, pointers @ c, pred)
          ) |>>| pre
      in
      verify (pre', body) (modules_a, a::vars, structures, procs) *)
    | _ -> [(pre, Formula.trueempty)]
    end

and verify_while pre b pr loc packs : Formula.t =
  p "Inv(A, b, P): ";
  p "A: ";
  Formula.pprint pre; p ",   b: "; BExp.pprint b; pn "";

  let xs : Var.t list = modv [] pr in
  let freevs : Var.t list = (freev pr) @@ (BExp.fv b) in
  let ys, _ = drop_common freevs xs in
  let iE01 = (fun x ->
      let nv : Var.t = newvar () in
      (x, (Exp.VAR nv, Exp.VAR nv))) |>>| xs in
  let iE02 = (fun y -> (y, (Exp.VAR y, Exp.VAR y))) |>>| ys in
  let iE0  = iE01 @ iE02 in
  pn "Symbolic interval based analysis begins: ";
  p "E0: "; Formula.pprint_intv iE0; pn "";
  let i1 = invariant_intv pre b pr iE0 iE0 xs ys packs loc in
  p "I1: "; Formula.pprint i1; pn "";
  let j1 = fst (List.split (verify ((conjunct i1 b), pr) packs)) in
  p "J1: "; Formula.pprint (List.hd j1); pn "";
  let res1 = entail "WHILE" j1 [i1] in
  if res1 then 
    pn "Symbolic Interval based invariant is valid"
  else
    pn "Symbolic Interval based invariant is invalid";
  pn "Loop count based analysis begins: ";
  let iE0 = (fun (a, (b, _)) -> (Term.encode a, Term.EXP b)) |>>| iE01 in
  p "E0: "; Formula.pprint_pairs iE0; pn "";
  let xs = Term.encode |>>| xs in
  let i2 = invariant_lc pre b pr [] iE0 xs ys packs loc in
  p "I2: "; Formula.pprint i2; pn "";
  let j2 = fst (List.split (verify ((conjunct i2 b), pr) packs)) in
  p "J2: "; Formula.pprint (List.hd j2); pn ""; pn "";
  let res2 = entail "WHILE" j2 [i2] in
  if res2 then 
    pn "Loop counter based invariant is valid"
  else
    pn "Loop counter based invariant is invalid";
  if res1 || res2 then
    neg_conjunct b pre
  else
    raise (StError "invariant failed")

and invariant_intv (fA : Formula.t) b pr iE (iE0:((Var.t*(Exp.t * Exp.t)) list)) xs ys packs loc : Formula.t =
  p "A: "; Formula.pprint fA; pn "";
  p "E: "; Formula.pprint_intv iE; pn "";
  let iE' = BExp.get_intervals iE ys b in (** [[b]](E) *)
  p "[[b]](E): "; Formula.pprint_intv iE'; pn "";
  let iE1 = verify_symb_intv iE' pr ys in
  p "E1: "; Formula.pprint_intv iE1; pn "";

  (** Newly added *)
  let fxA = (fun a x ->
      let fresh = newvar () in
      let a' = Formula.substitute (Term.encode x) (Term.encode fresh) a loc in
      (fun (exs, b, c, d) -> (exs @ [fst fresh], b, c, d)) |>>| a'
    ) |->> (fA, xs) in

  let fxA_b = (conjunct fxA b) in (** A & b, [[b]](E) *)
  p "Ex x.A & b, [[b]](E): "; Formula.pprint fxA_b; pn "";

  let fxA_b_tE = formula_of_intv fxA_b iE in  (** A & b & ~E, [[b]](E) *)
  (* let fxA_b_tE = (fun f x -> ex x f) |->> (fA_b_tE, xs) in *)
  p "Ex x.A & b & ~E, [[b]](E): "; Formula.pprint fxA_b_tE; pn "";

  let fB  = fst (List.hd (verify (fxA_b_tE, pr) packs)) in (** Verify(A & b & ~E, P), [[P]]([[b]](E)) *)
  p "B:"; Formula.pprint fB; pn "";

  let fB_tE1 = formula_of_intv fB iE1 in
  p "B & ~E1: "; Formula.pprint fB; pn "";

  let tE = formula_of_intv Formula.empty iE in

  p "~E: "; Formula.pprint tE;  pn "";
  if entail "INV" [fB_tE1] [tE] then
    begin
      let fA' =
        (fun a (x, (Exp.VAR y,_)) ->
          let a' = Formula.substitute (Term.encode x) (Term.encode y) a loc in
          ex y a'
        ) |->> (fA, iE0)
      in
    p "Ex x0.A[x:=x0]: "; Formula.pprint fA';  pn "";
    let fres1 = formula_of_intv fA' iE0 in
    let fres2 = formula_of_intv fA' iE1 in
    let res = fres1 @ fres2 in
    p "res: "; Formula.pprint res;  pn "";
    res
    end
  else
    let e = nabla fB iE iE1 ys in
    p "E nabla E1: "; Formula.pprint_intv e;  pn "";
    invariant_intv fA b pr e iE0 xs ys packs loc



and invariant_lc (fA : Formula.t) b pr _ (lE0:((Term.t * Term.t) list)) xs ys packs loc : Formula.t =
  let lE = verify_loop_counter lE0 pr ys xs in
  p "E: "; Formula.pprint_pairs lE; pn "";
  let es =
    (fun x ->
      let t = get_E_t lE xs x in
      let fvs = Term.encode |>>| (Term.fv t) in
      if common fvs xs = [] then
        let et = Term.toExp t in
        let x0 = Term.toExp (get_E_t lE0 xs x) in
        let t = Exp.eval (Exp.BINOP (et, Op.SUB, x0)) in
        x, x0, t
      else
        raise (StError "Fail 0")
    ) |>>| xs
  in
  p "(x,x0,t): "; 
  iterS (fun (x, x0, t) -> p "("; Term.pprint x; p ", "; Exp.pprint x0; p ", "; Exp.pprint t; p ")") "; " es; pn "";
  let fA' = (fun a (x, t) ->
      let a' = Formula.substitute x t a loc in
      ex (Term.decode t) a'
    ) |->> (fA, lE0) in
  let lambda = ("'L", []) in
  let ret = (fun a (x, x0, t) ->
      let t_lambda = Exp.eval (Exp.BINOP (t, Op.MUL, Exp.VAR lambda)) in
      let x0_t_lambda = Exp.eval (Exp.BINOP (x0, Op.ADD, t_lambda)) in
      let eq = BExp.UNIT (x, Op.EQ, Term.EXP x0_t_lambda) in
      conjunct a eq
    ) |->> (fA', es) in
  ex lambda ret

