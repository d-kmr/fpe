open Ftools
open VcpBase
module C = Cabs
         
let if_mode = ref false

let print_map ls =
  iterS (fun (a,b) -> Cprint.print_expression a; p " ==> "; Cprint.print_expression b) "; " ls
            
let one_g = Cabs.CONSTANT (Cabs.CONST_INT "1")

let rec extract_ref_call ?lhs:(lhs=false) ?precond:(pc=[]) ?level:(lvl=true) ?is_call:(lc=false) map exp =
  pn_s "EXT" "";
  pf_s "EXT" Cprint.print_expression exp;
  pf_s "EXT" print_string "\n";
  pf_s "EXT" pb lvl;
  pf_s "EXT" print_string "\n";
  pf_s "EXT" pb lhs;
  pf_s "EXT" print_string "\n";
  let exp' =
  match exp with
  | Cabs.NOTHING -> (exp, map)
  | C.CAST (([C.SpecType C.Tsizet], C.JUSTBASE), C.SINGLE_INIT (C.UNARY (C.ADDROF, e))) ->
  
     let nv   = Cabs.VARIABLE (new_prog_var ()) in
     let exp1 = exp in 
     (nv, (nv,exp1)::map)
     
  | Cabs.UNARY (Cabs.ADDROF, Cabs.PAREN(Cabs.MEMBEROF (exp, field)))
  | Cabs.UNARY (Cabs.ADDROF, Cabs.PAREN(Cabs.MEMBEROFPTR (exp, field)))
  | Cabs.UNARY (Cabs.ADDROF, Cabs.MEMBEROF (exp, field))
  | Cabs.UNARY (Cabs.ADDROF, Cabs.MEMBEROFPTR (exp, field)) ->
     pn_s "EXT" "@3";
     let (exp', map')     = extract_ref_call ~level:false map exp in
     
     begin
       (* match exp' with
         Cabs.VARIABLE _ ->
          let exp'' = Cabs.UNARY (Cabs.ADDROF, Cabs.MEMBEROFPTR (exp', field)) in
          pf_s "EXT" Cprint.print_expression exp'';
          pf_s "EXT" print_string "\n";
     
         (exp'', map')
       | _ -> *)
         let nv   = Cabs.VARIABLE (new_prog_var ()) in
         let exp1 = Cabs.UNARY (Cabs.ADDROF, Cabs.MEMBEROFPTR (exp', field)) in 
         if lc then
           (exp1, map')
         else
           (nv, (nv,exp1)::map')
     end
  | Cabs.UNARY (Cabs.MEMOF, pointer_exp) ->                                                           (** *x *)
     (** *x *)
     begin
       pn_s "EXT" "@4";
       let (pointer_exp', map')    = extract_ref_call ~level:false map pointer_exp in
       match pointer_exp' with
       | Cabs.UNARY (Cabs.ADDROF, e2)
       | Cabs.PAREN (Cabs.UNARY (Cabs.ADDROF, e2)) ->
          (e2, map')
       | _ ->
          
          let expression              = Cabs.UNARY (Cabs.MEMOF, pointer_exp') in
          
          let substitute_var          = (fun (k, v) -> not lhs && v = expression) |>- map' in
          begin
            match substitute_var with
            | [] ->
               let nv = Cabs.VARIABLE (new_prog_var ()) in
               if lhs then
                 (expression, map')
               else
                 (nv, (nv, expression) :: map')
               
            | (k, v)::_ ->
               (k, map')
          end
     end
    (*
  | Cabs.UNARY (op, Cabs.MEMBEROF (expression, str))
    | Cabs.UNARY (op, Cabs.MEMBEROFPTR (expression, str)) when
         op = Cabs.PREINCR
         || op = Cabs.PREDECR
         || op = Cabs.POSINCR
         || op = Cabs.POSDECR ->
     let (expression', map') = extract_ref_call ~level:false map expression in
     let temp = Cabs.UNARY (op, expression') in
     let (temp', map'') = extract_ref_call ~level:false map' temp in
     *)

  | Cabs.UNARY (op, operand) when op = Cabs.PREINCR || op = Cabs.PREDECR ->

     
     begin
       match operand with
         Cabs.VARIABLE _ ->
     
         let cop = if op = Cabs.PREINCR then Cabs.ADD_ASSIGN else Cabs.SUB_ASSIGN in

         let expression = Cabs.BINARY (cop, operand, one_g) in
         extract_ref_call ~level:lvl map expression

       | Cabs.MEMBEROF (operand, field)
         | Cabs.MEMBEROFPTR (operand, field) ->
          (**
             ++ operand->field ;
             ==>
             t1 = operand'->field;
             --t1;
             operand'->field = t1;
           *)
          
          let (operand', map') = extract_ref_call ~level:false map operand in
          
          let t1 = Cabs.VARIABLE (new_prog_var ()) in
          let st1 = (t1, Cabs.MEMBEROF (operand', field)) in
          
          let expression = Cabs.UNARY (op, t1) in
          let (expression', map'')  = extract_ref_call ~level:false [] expression in

          let st3 = (Cabs.MEMBEROF (operand', field), expression') in

          let maps = st3::map''@[st1]@map' in
          
          (t1, maps)
       | Cabs.UNARY (Cabs.MEMOF, operand) ->
          (**
             --( * operand);
             ==>
             t1 = ( * operand');
             --t1;
             ( *operand) = t1
             t1
           *)
          
          let (operand', map') = extract_ref_call ~level:false map operand in
          
          let t1 = Cabs.VARIABLE (new_prog_var ()) in
          let st1 = (t1, Cabs.UNARY (Cabs.MEMOF, operand')) in

          let expression = Cabs.UNARY (op, t1) in
          let (expression', map'')  = extract_ref_call ~level:false [] expression in

          let st3 = (Cabs.UNARY (Cabs.MEMOF, operand'), expression') in

          let maps = st3::map''@[st1]@map' in
          
          (t1, maps)
       | Cabs.INDEX (exp1, exp2) ->
          (**
             --exp1[exp2] --;
             ==>
             t1 = ( * (exp1'+exp2'));
             --t1;
             ( * (exp1'+exp2')) = t1
             t1
           *)
          
          let (exp1', map') = extract_ref_call ~level:false map exp1 in
          let (exp2', map'') = extract_ref_call ~level:false map' exp2 in
          
          let t1 = Cabs.VARIABLE (new_prog_var ()) in
          let st1 = (t1, Cabs.UNARY (Cabs.MEMOF, Cabs.BINARY (Cabs.ADD, exp1', exp2'))) in

          let expression = Cabs.UNARY (op, t1) in
          let (expression', map'')  = extract_ref_call ~level:false [] expression in

          let st3 = (Cabs.UNARY (Cabs.MEMOF, Cabs.BINARY (Cabs.ADD, exp1', exp2')), expression') in

          let maps = st3::map''@[st1]@map' in
          
          (t1, maps)
       | Cabs.PAREN (expression) ->
          let (expression', map') = extract_ref_call ~level:false map (Cabs.UNARY (op, expression)) in
          (Cabs.PAREN(expression'), map')
       | _ ->
          Cprint.print_expression (Cabs.UNARY (op, operand)); pn "";
          raise (StError "@@@@@@@@@@@@@ NON-SUPPORTED ++/--")
     end
    
  | Cabs.UNARY (Cabs.POSDECR as op, operand)
  | Cabs.UNARY (Cabs.POSINCR as op, operand) ->                                                   (** x++;        x++     y = x++;
                                                                                                        x[i]++;     x[i]++  y = x[i]++;
                                                                                                        x->f++;     x->f++  y = x->f++;
                                                                                                        ++x;        a = x; ++x; a
                                                                                                        ++x[i];     a = x[i]; ++x[i]; a
                                                                                                        ++x->f;     a = x->f; ++x->f; a *)
     pn_s "EXT" "@7";

     begin
       match operand with
         Cabs.VARIABLE _ ->
         
         let (operand', map') = extract_ref_call ~level:false map operand in
         let op' = if op = Cabs.POSINCR then Cabs.PREINCR else Cabs.PREDECR in
         let expression = Cabs.UNARY (op', operand') in

         
         if lvl then
           begin
             extract_ref_call map' expression
           end
         else
           begin
             
             let carry                 = Cabs.VARIABLE (new_prog_var ()) in
             let map''                 = (carry, operand') :: map' in
             
             let (_, map'')  = extract_ref_call ~level:false map'' expression in
             
             (carry, map'')
           end
       | Cabs.MEMBEROF (operand, field)
         | Cabs.MEMBEROFPTR (operand, field) ->
          (**
             operand->field --;
             ==>
             t1 = operand'->field;
             t2 = t1;
             --t1;
             operand'->field = t1
             t2
           *)
          
          let (operand', map') = extract_ref_call ~level:false map operand in
          
          let t1 = Cabs.VARIABLE (new_prog_var ()) in
          let st1 = (t1, Cabs.MEMBEROF (operand', field)) in

          let dummy = Cabs.VARIABLE ("###dummy") in
          let stdummy = (dummy, dummy) in 
          
          let t2 = Cabs.VARIABLE (new_prog_var ()) in
          let st2 = (t2, t1) in

          let op' = if op = Cabs.POSINCR then Cabs.PREINCR else Cabs.PREDECR in
          let expression = Cabs.UNARY (op', t1) in
          let (expression', map'')  = extract_ref_call ~level:false [] expression in

          let st3 = (Cabs.MEMBEROF (operand', field), expression') in

          let maps = st3::map''@[st2;stdummy;st1]@map' in
         
          (t2, maps)
       | Cabs.UNARY (Cabs.MEMOF, operand) ->
          (**
             ( * operand) --;
             ==>
             t1 = ( * operand');
             t2 = t1;
             --t1;
             ( *operand) = t1
             t2
           *)
          
          let (operand', map') = extract_ref_call ~level:false map operand in
          
          let t1 = Cabs.VARIABLE (new_prog_var ()) in
          let st1 = (t1, Cabs.UNARY (Cabs.MEMOF, operand')) in

          let dummy = Cabs.VARIABLE ("###dummy") in
          let stdummy = (dummy, dummy) in 
          
          let t2 = Cabs.VARIABLE (new_prog_var ()) in
          let st2 = (t2, t1) in

          let op' = if op = Cabs.POSINCR then Cabs.PREINCR else Cabs.PREDECR in
          let expression = Cabs.UNARY (op', t1) in
          let (expression', map'')  = extract_ref_call ~level:false [] expression in

          let st3 = (Cabs.UNARY (Cabs.MEMOF, operand'), expression') in

          let maps = st3::map''@[st2;stdummy;st1]@map' in
         
          (t2, maps)
       | Cabs.INDEX (exp1, exp2) ->
          (**
             exp1[exp2] --;
             ==>
             t1 = ( * (exp1'+exp2'));
             t2 = t1;
             --t1;
             ( * (exp1'+exp2')) = t1
             t2
           *)
          
          let (exp1', map') = extract_ref_call ~level:false map exp1 in
          let (exp2', map'') = extract_ref_call ~level:false map' exp2 in
          
          let t1 = Cabs.VARIABLE (new_prog_var ()) in
          let st1 = (t1, Cabs.UNARY (Cabs.MEMOF, Cabs.BINARY (Cabs.ADD, exp1', exp2'))) in

          let dummy = Cabs.VARIABLE ("###dummy") in
          let stdummy = (dummy, dummy) in 
          
          let t2 = Cabs.VARIABLE (new_prog_var ()) in
          let st2 = (t2, t1) in

          let op' = if op = Cabs.POSINCR then Cabs.PREINCR else Cabs.PREDECR in
          let expression = Cabs.UNARY (op', t1) in
          let (expression', map'')  = extract_ref_call ~level:false [] expression in

          let st3 = (Cabs.UNARY (Cabs.MEMOF, Cabs.BINARY (Cabs.ADD, exp1', exp2')), expression') in

          let maps = st3::map''@[st2;stdummy;st1]@map' in
         
          (t2, maps)
       | Cabs.PAREN (expression) ->
          let (expression', map') = extract_ref_call ~level:false map (Cabs.UNARY (op, expression)) in
          (Cabs.PAREN(expression'), map')

       | _ ->
          Cprint.print_expression (Cabs.UNARY (op, operand)); pn "";
          raise (StError "@@@@@@@@@@@@@ NON-SUPPORTED ++/--")
     end
  | Cabs.UNARY (Cabs.ADDROF, Cabs.PAREN (expression) ) ->
     pn_s "EXP" "UNARY: ADDROF";  (** &(x[i]) == (x+i) *)

     extract_ref_call ~level:lvl ~is_call:lc map (Cabs.UNARY (Cabs.ADDROF, expression))
  | Cabs.UNARY (Cabs.ADDROF, expression ) as exp ->
     if lc then
       begin
        
         (exp, map)
       end
     else
       begin
         pn_s "EXT" "@9";
         let (exp1, map')            = extract_ref_call ~level:lvl map expression in
       
         match map' with
           (y', Cabs.UNARY (Cabs.MEMOF, e2))::xs |
           (y', Cabs.PAREN (Cabs.UNARY (Cabs.MEMOF, e2)))::xs when y'=exp1->
            (e2, xs)
           | _ ->
              let nv = Cabs.VARIABLE (new_prog_var ()) in
              (nv, (nv,Cabs.UNARY (Cabs.ADDROF, exp1))::map')
       end
  | Cabs.UNARY (unary_operator, expression) ->
     pn_s "EXP" "UNARY: expression";
     let (expression', map')     = extract_ref_call ~level:false map expression in
     (Cabs.UNARY (unary_operator, expression'), map')
  | Cabs.LABELADDR (_) ->
     (exp, map)  (* GCC's && Label *)
  | Cabs.BINARY (Cabs.ASSIGN, Cabs.INDEX (l_part, r_index), rhs) ->
     (** x[i][j] = rhs *)
     begin
       let rec trans_exp map'    = function
         | Cabs.INDEX (exp_11, exp_12) ->
            let (exp_12', map'')    = extract_ref_call ~level:false map' exp_12 in
            let (exp_11', map'')    = trans_exp map'' exp_11 in
            (Cabs.INDEX (exp_11', exp_12'), map'')
         | exp -> extract_ref_call ~level:false map' exp (* (exp, map') *)
       in
       let (rhs', map')          = extract_ref_call ~level:false map rhs in
       let (r_index', map')      = extract_ref_call ~level:false map' r_index in
       let (l_part', map'')      = trans_exp map' l_part in
       if lvl then                                                                                     (** Outside. As a Command. i.e. x[][] = 0; *)
         (Cabs.BINARY (Cabs.ASSIGN, Cabs.INDEX (l_part', r_index'), rhs'), map'')
       else                                                                                            (** Inside. i.e. x + (y[1] = z),
                                                                                                           x + (y[y[1] = z] = z)  . Extract a command *)
         begin
           let pre_command1        = (Cabs.INDEX (l_part', r_index'), rhs') in
           let nv                  = Cabs.VARIABLE (new_prog_var ()) in
           let pre_command2        = (nv, Cabs.INDEX (l_part', r_index')) in
           
           (nv, pre_command1::pre_command2::map'')
         end
     end     
    | Cabs.BINARY (Cabs.ASSIGN, Cabs.MEMBEROF (pointer_exp, field), rhs_exp) (** Match special pattern here for array mutation *)
    | Cabs.BINARY (Cabs.ASSIGN, Cabs.MEMBEROFPTR (pointer_exp, field), rhs_exp) ->
     (** A.f = ?  *)
     (** A->f = ? *)
     pn_s "EXT" "@11";
     let (rhs_exp',      map')   =   extract_ref_call ~level:false map   rhs_exp in
     let (pointer_exp',  map')   =
       begin
         match pointer_exp with
           Cabs.INDEX (lpart, rpart) ->
            let (rpart', map'') = extract_ref_call ~level:false map'  rpart in
            let (lpart', map''') = extract_ref_call ~level:false map''  lpart in
           Cabs.BINARY (Cabs.ADD, lpart', rpart'), map'''
         | _ ->
            extract_ref_call ~level:false map'  pointer_exp
       end
     in
     if lvl && not !if_mode then (** Outside. x->f = y; *)
       (
         (Cabs.BINARY (Cabs.ASSIGN, Cabs.MEMBEROF (pointer_exp', field), rhs_exp'),    map')
       )
     else
       ((** Inside.  x + (y->f = z) *)
        let nv = Cabs.VARIABLE (new_prog_var ()) in
        let star_e = Cabs.MEMBEROF (pointer_exp', field) in
          (nv, (nv, star_e) :: (star_e, rhs_exp') :: map')
       )
  | Cabs.BINARY (Cabs.ASSIGN, Cabs.UNARY(Cabs.MEMOF, exp1), exp2) ->
     (** *exp1 = exp2 *)
     let (rhs, rmap) = extract_ref_call ~level:false map exp2 in
     let (lhs, lmap) = extract_ref_call ~level:false rmap exp1 in
       
     if !if_mode || not lvl then
       (** *x = y  
           ---->
           *x = y;
           nv = *x;
           nv
        *)
       let nv = Cabs.VARIABLE (new_prog_var ()) in
       let m2 = (Cabs.UNARY(Cabs.MEMOF, lhs), rhs) in
       let m1 = (nv, Cabs.UNARY(Cabs.MEMOF, lhs)) in
       (nv, m1::m2::lmap)
     else
       Cabs.BINARY (Cabs.ASSIGN, Cabs.UNARY(Cabs.MEMOF, lhs), rhs), lmap

  (* | Cabs.BINARY (Cabs.ASSIGN, Cabs.PAREN ((Cabs.VARIABLE (var) as lhs)), rhs) *)
  (*| Cabs.BINARY (Cabs.ASSIGN, lhs, (Cabs.BINARY(Cabs.ASSIGN, _, _) as rhs)) ->
     let (rhs', map') = extract_ref_call ~level:lvl map rhs in
     begin
       match rhs' with
         Cabs.BINARY(Cabs.ASSIGN, lh, rh) ->
         (Cabs.BINARY (Cabs.ASSIGN, lhs, lh), (lh, rh)::map')
       | _ -> raise (StError "x=y=z problem")
     end *)
  | Cabs.BINARY (Cabs.ASSIGN, Cabs.PAREN (Cabs.VARIABLE (var) as lhs), rhs)
  | Cabs.BINARY (Cabs.ASSIGN, (Cabs.VARIABLE (var) as lhs), rhs) ->
     (** x = rhs *)
     
     let (rhs', map')   =   extract_ref_call ~level:false map   rhs in
     if !if_mode || lvl = false then          (** Inside an expression *)
       (
         (lhs, (lhs, rhs')::map')
       )
     else(
       (Cabs.BINARY (Cabs.ASSIGN, lhs, rhs'), map')
     )
  (* | Cabs.BINARY (Cabs.NE, Cabs.UNARY (Cabs.MEMOF, exp00), Cabs.CONSTANT (Cabs.CONST_INT "0"))
    (* | Cabs.BINARY (Cabs.NE, Cabs.UNARY (Cabs.MEMOF, exp00), Cabs.CONSTANT (Cabs.CONST_CHAR ['0'])) *) 
    | Cabs.BINARY (Cabs.NE, Cabs.UNARY (Cabs.MEMOF, exp00), Cabs.VARIABLE ("NULL"))  when !if_mode ->
     (** *s != 0 *)
     (** *s != NULL *)
     if_mode.contents <- false;
     let (exp_12', map'')    = extract_ref_call ~level:false map exp00 in
     if_mode.contents <- true;
     (Cabs.UNARY (Cabs.MEMOF, exp_12'), map'')
     (** X ? Y *) *)
  | Cabs.BINARY (binary_operator, expression1, expression2) ->   (** Other binary operators *)
     pn_s "EXT" "Other Ordinary Binary Operator with Assignment";
     let (expression', map')     = extract_bin lvl map binary_operator expression2 expression1 in
     (expression', map')
  | Cabs.QUESTION (exp1, exp2, exp3) ->
     let (exp1, map')            = extract_ref_call ~level:false map exp1 in
     let exp1' = if List.length pc = 0 then
                   exp1
                 else
                   Cabs.BINARY (Cabs.BAND, exp1, List.hd pc)
     in
     let (exp2, map')            = extract_ref_call ~precond:[exp1'] ~level:false map' exp2 in
     let exp1'' = if List.length pc = 0 then
                   Cabs.UNARY (Cabs.NOT, exp1)
                 else
                   Cabs.BINARY (Cabs.BAND, Cabs.UNARY (Cabs.NOT, exp1), List.hd pc)
     in
     let (exp3, map')            = extract_ref_call ~precond:[exp1''] ~level:false map' exp3 in
     let nv                      = Cabs.VARIABLE (new_prog_var ()) in

     
     (nv, (nv, Cabs.QUESTION (exp1', exp2, exp3)) :: map')
  | Cabs.CAST ((specifier, decl_type), init_expression) ->
     begin
       pn_s "EXT" "@CAST";
       let rec f map i_e         =
         match i_e with
         | Cabs.SINGLE_INIT (expression) ->
            begin
              let (exp, map') = extract_ref_call ~lhs:lhs ~level:false map expression in
              
              
              
              let map'' = (fun (a,b) ->
                  
                if a = exp then
                  begin
                    let a' =
                      match a with
                        C.CAST (_, _) ->
                         a
                      | _ ->
                         Cabs.CAST ((specifier, decl_type), Cabs.SINGLE_INIT exp)
                    in
                    (a',b)
                  end
                else
                  (a,b)
                ) |>>| map' in

              let nv = Cabs.VARIABLE (new_prog_var ()) in
              (nv, (nv, Cabs.CAST ((specifier, decl_type), Cabs.SINGLE_INIT (exp)))::map'')
            end
         | Cabs.COMPOUND_INIT xss ->
            let yss               = snd |>>| xss in
            let yss' =
              try
                List.hd yss
              with
                _ -> raise (StError ("extract_ref_call - Cabs.CAST"))
            in
            f map yss'
         | _ -> (Cabs.NOTHING, map)
       in

       let (ie', map') = f map init_expression in
       
       (ie', map')
     end
  | Cabs.CALL (Cabs.VARIABLE s, l_expression) when Bytes.length s > 1 && Bytes.sub s 0 1 = "@" ->
     begin
       let (expression', map')   =
         try
           extract_ref_call ~level:false map (List.hd l_expression)
         with
           _ -> raise (StError ("No body of " ^ s))
       in
       
       let d = Cabs.CALL (Cabs.VARIABLE s, [expression']) in
       (d, map')
     end
  | Cabs.CALL (expression, l_expression)  ->
     begin
       let (expression', map')     = extract_ref_call ~level:false map expression in
       let (l_expression', map'')   = extract_ref_call_all ~is_call:true map' (List.rev l_expression) in
       (* Cprint.print_expression (Cabs.CALL (expression', l_expression')); pn ""; *)
       (* let old_pair                = (fun (_, v) -> v = Cabs.CALL (expression', l_expression')) |>- map' in
       match old_pair with
       | [] -> *)
          let nv    = Cabs.VARIABLE (new_prog_var ()) in
          let map'' = (nv, Cabs.CALL (expression', List.rev l_expression'))::(map'') in
          (* iterS (fun (a,b) -> Cprint.print_expression a; p "="; Cprint.print_expression b) " -- " map''; *)
          ( nv, map'')
       (* | (k, _)::_ ->
          (k, map') *)
     end
  | Cabs.COMMA (l_expression) ->
     let (l_expression', map')     = extract_ref_call_all map l_expression in
     (Cabs.COMMA (l_expression'), map')
  | Cabs.CONSTANT _ -> (exp, map)
  | Cabs.PAREN (expression) ->
     
     let (expression', map')       = extract_ref_call ~lhs:lhs ~level:lvl map expression in
     dbg "EXT" "map@PAREN:\n" print_map map' ;
     begin
       match expression' with
         Cabs.PAREN (exp) -> (expression', map')
       | _ ->
          if lhs then
            (expression', map')
          else
            (Cabs.PAREN (expression'), map')
     end
  | Cabs.VARIABLE ( str ) ->
     (exp, map)
  | Cabs.EXPR_SIZEOF _ -> (exp, map)
  | Cabs.TYPE_SIZEOF _ -> (exp, map)
  | Cabs.EXPR_ALIGNOF _ -> (exp, map)
  | Cabs.TYPE_ALIGNOF _ -> (exp, map)
  | Cabs.INDEX (exp00, exp01) when !if_mode ->
     (** x[i][j] *)
     if_mode.contents <- false;
     
     let (exp00', map')    = extract_ref_call ~level:false map exp00 in
     
     
     let (exp01', map'')    = extract_ref_call ~level:false map' exp01 in
     let nv                  = Cabs.VARIABLE (new_prog_var ()) in
     let d = Cabs.UNARY (Cabs.MEMOF, Cabs.BINARY(Cabs.ADD, exp00', exp01')) in

     let map''' = (nv, d)::map'' in

     if_mode.contents <- true;
     (nv, map''')
  | Cabs.INDEX (expression1, expression2) ->  (** expression1[expression2]  *)
     
     let rec get_indices           = function
       | Cabs.INDEX (exp1, exp2) ->    (** exp1[exp2]  *)
          let (exp1', map')         = get_indices exp1 in
          let (exp2', map'')        = extract_ref_call ~level:false map' exp2 in
          begin
            match exp2' with
            | Cabs.INDEX (_, _) ->
               let nv                = Cabs.VARIABLE (new_prog_var ()) in
               (nv, (nv, exp2') :: map'')
            | _ -> (** (Cabs.INDEX (exp1', exp2'), map'') *) (** disabled in Oct 22 *)
               (Cabs.UNARY (Cabs.MEMOF, Cabs.BINARY(Cabs.ADD, exp1', exp2')), map'')
          end
       | exp -> extract_ref_call ~level:false map exp
     in
     let nv                        = Cabs.VARIABLE (new_prog_var ()) in
     let (exp, map')               = get_indices (Cabs.INDEX (expression1, expression2)) in
     
     (nv, (nv, exp) :: map')
  | Cabs.MEMBEROF (expression, str)
  | Cabs.MEMBEROFPTR (expression, str) as e ->
     begin
       pn_s "EXT" "@20";
       let old_pair                = (fun (_, v) -> v = e) |>- map in
       match old_pair with
       | [] ->
          let (expression', map')   = extract_ref_call ~level:false map expression in
          let nv                    = Cabs.VARIABLE (new_prog_var ()) in
          let exp1 = Cabs.MEMBEROFPTR (expression', str) in
          pf_s "EXT" Cprint.print_expression nv;
          pf_s "EXT" print_string "=";
          pf_s "EXT" Cprint.print_expression exp1;
          pf_s "EXT" print_string "\n";
     
          let map'' = (nv, exp1)::map' in
          (* Cprint.print_expression nv; pn " ---"; *)
          (nv, map'')
       | (k, _) :: _ ->
          pf_s "EXT" print_string "Auto_matched\n";
          (k, map)
     end
  | x -> pn_s "EXT" "~~~~~~~~~";
         (x, map)
  in
  dbg "EXT" "exp-->exp':" (fun () -> Cprint.print_expression exp; p " --> "; Cprint.print_expression (fst exp')) ();
  exp'

and extract_bin outside map op rhs lhs =
  dbg "EXT" "Res (BinExt)B:" Cprint.print_expression (Cabs.BINARY(op, lhs, rhs));
    let op_pairs = [
      (Cabs.ADD_ASSIGN, Cabs.ADD);
      (Cabs.SUB_ASSIGN, Cabs.SUB);
      (Cabs.MUL_ASSIGN, Cabs.MUL);
      (Cabs.DIV_ASSIGN, Cabs.DIV);
      (Cabs.MOD_ASSIGN, Cabs.MOD);
      (Cabs.SHL_ASSIGN, Cabs.SHL);
      (Cabs.SHR_ASSIGN, Cabs.SHR);
      (Cabs.BAND_ASSIGN, Cabs.BAND);
      (Cabs.BOR_ASSIGN, Cabs.BOR);
      (Cabs.XOR_ASSIGN, Cabs.XOR)
    ] in
    if op |<- (fst |>>| op_pairs) then                                                          (** Complex binary operations e.g. x += y; *)
      begin
        (* Cprint.print_expression (Cabs.BINARY (op, lhs, rhs)); pn " ***";
        pb !if_mode; pn ""; *)
      let op_pair       =
        try
          List.find (fun x -> fst x = op) op_pairs
        with
          _ -> raise (StError ("extract_bin - "))
      in
      
      let op'           = snd op_pair in
      let (lhs', map1)  = extract_ref_call ~lhs:true ~level:false map lhs in
      let (rhs', map2)  = extract_ref_call ~level:false map1 rhs in
      let expression    = Cabs.BINARY (Cabs.ASSIGN, lhs, Cabs.BINARY (op', lhs', rhs')) in
      let (exp, map')   = extract_ref_call ~level:outside map2 expression in
      exp, map'
      end
    else                                                                                        (** Simple binary operations e.g. x + y *)
      begin
        pn_s "EXT" "Binary: Else";
        let islhs = if op = Cabs.ASSIGN then true else false in 
        
        let (rhs', map')  = extract_ref_call ~level:outside map   rhs in
        let (lhs', map')  = extract_ref_call ~lhs:islhs ~level:outside map'  lhs in
        let lhs'', map'' =
          match lhs' with
            Cabs.UNARY (Cabs.ADDROF, _) -> 
            let nv                    = Cabs.VARIABLE (new_prog_var ()) in
            (nv, (nv, lhs')::map')
          | _ -> (lhs', map')
        in
        let rhs'', map'' =
          match rhs' with
            Cabs.UNARY (Cabs.ADDROF, _) -> 
            let nv                    = Cabs.VARIABLE (new_prog_var ()) in
            (nv, (nv, rhs')::map'')
          | Cabs.BINARY (Cabs.ASSIGN, rlhs, rrhs) ->
             (rrhs, (rlhs, rrhs)::map'')
          | _ -> (rhs', map'')
        in
        let res = Cabs.BINARY (op, lhs'', rhs'') in
        dbg "EXT" "Res (BinExt)E:" Cprint.print_expression res;
        dbg "EXT" "Map:" print_map map'';
        (res, map'')
      end

  and extract_ref_call_all ?is_call:(lc=false) map = function
    | [] ->
       ([], map)
    | x::xs ->
      
       let (xs', map') = extract_ref_call_all ~is_call:lc map xs in
       let (x', map'') = extract_ref_call ~level:false ~is_call:lc map' x in
       (x'::xs', map'')


  let rec extract_ref_call_init_name map exp =
    match exp with
    | Cabs.NO_INIT -> (exp, map)
    | Cabs.SINGLE_INIT (expression) ->
      let (expression', map') = extract_ref_call map expression in
      (Cabs.SINGLE_INIT expression', map')
    | Cabs.COMPOUND_INIT xs ->
      let g ((iw : Cabs.initwhat), (ie:Cabs.init_expression)) m =
        let (ie', m') = extract_ref_call_init_name m ie in ((iw, ie'), m')
      in
      let rec f m = function
        | [] -> ([], m)
        | y::ys ->
          let (ys', m') = f m ys in
          let (y', m') = g y m' in
          ((y'::ys'), m')
      in
      let (xs', map') = f map xs in
      (Cabs.COMPOUND_INIT xs', map')

  and extract_ref_call_l_init_name  map = function
    | [] -> ([], map)
    | (name, x)::xs ->
      let (xs', map') = extract_ref_call_l_init_name map xs in
      let (x', map') = extract_ref_call_init_name  map' x in
      ((name, x')::xs, map')


  let rec get_assignments_cabs l = function
    | [] -> []
    | (k', var)::xs ->
      let xs' = get_assignments_cabs l xs in
      let r = Cabs.COMPUTATION (Cabs.BINARY (Cabs.ASSIGN, k', var), l) in
      xs' @ [r]


  let rec extract_statement x =
    let dl = {Cabs.lineno = 0;filename = "";byteno = 0;ident = 0;} in
    match x with
    | Cabs.DEFINITION (definition) ->
       let (map, def, lc) = extract_definition definition in
       (map, [Cabs.DEFINITION def], lc)
    | Cabs.COMPUTATION (Cabs.CALL (expression, expressions), cl) ->
       let (expression', map1) = extract_ref_call [] expression in
       let (expressions', map2) =
         (fun (exps', map') exp ->
           let (exp', map'') = extract_ref_call map' exp in
           (exps' @ [exp'], map'')
         ) |->> (([],map1), expressions) in
       let x' = Cabs.COMPUTATION (Cabs.CALL (expression', expressions'), cl) in
       (map2, [x'], cl)
    | Cabs.COMPUTATION (expression, cl) ->
       let (expression', map) = extract_ref_call [] expression in
       let x' = Cabs.COMPUTATION (expression', cl) in
       (map, [x'], cl)
    | Cabs.BLOCK (block, l) ->
       let bstmts' = extract_statements block.Cabs.bstmts in
       let x' = Cabs.BLOCK ({Cabs.blabels = block.Cabs.blabels; battrs = block.Cabs.battrs; bstmts = bstmts'}, l) in
       ([], [x'], dl)
    | Cabs.SEQUENCE (statement1, statement2, cl) ->
       let statements1 = extract_statements [statement1] in
       let statements2 = extract_statements [statement2] in
       let xs' = statements1 @ statements2 in
       ([], xs', cl)
    | Cabs.IF (expression, statement1, statement2, cl) ->
       let (expression', map) = extract_ref_call [] expression in
       let statements1' = extract_statements [statement1] in
       let statement1' =
         if List.length statements1' = 1 then
           List.hd statements1'
         else
           Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = statements1'}, cl)
       in
       let statements2' = extract_statements [statement2] in
       let statement2' =
         if List.length statements2' = 1 then
           List.hd statements2'
         else
           Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = statements2'}, cl)
       in
       let x' = Cabs.IF (expression', statement1', statement2', cl) in
       (map, [x'], cl)
    | Cabs.WHILE (formula, expression, statement, cl) ->
       let (expression', map) = extract_ref_call [] expression in
       let pre = get_assignments_cabs cl map in
       let statements' = extract_statements [statement] in
       let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = (statements'@pre)}, cl) in
       let x' = Cabs.WHILE (formula, expression', statement', cl) in
       (map, [x'], cl)
    | Cabs.DOWHILE (formula, expression, statement, cl) ->
       let (expression', map) = extract_ref_call [] expression in
       let pre = get_assignments_cabs cl map in
       let statements' = extract_statements [statement] in
       let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = (statements'@pre)}, cl) in
       let x' = Cabs.DOWHILE (formula, expression', statement', cl) in
       ([], [x'], cl)
    | Cabs.FOR (formula, for_clause, expression_cond0, expression2, statement, cl) ->
       begin
         let (map, for_clause') =
           match for_clause with
           | Cabs.FC_EXP expression ->
              let (expression', map') = extract_ref_call [] expression in
              (map', Cabs.COMPUTATION (expression', cl))
           | Cabs.FC_DECL definition ->
              let (map, def, _) = extract_definition definition in
              (map, Cabs.DEFINITION def)
         in
         let (expression_cond0', map1) = extract_ref_call [] expression_cond0 in
         let pre_cond = get_assignments_cabs cl map1 in
         let pre_init = for_clause'::pre_cond in
         let (expression2', map2) = extract_ref_call [] expression2 in
         let pre_cont = get_assignments_cabs cl map2 in
         let statements' = extract_statements [statement] in
         let statements2' =
           match expression2' with
           | Cabs.COMMA el -> (fun e -> Cabs.COMPUTATION (e, cl)) |>>| el
           | e -> [Cabs.COMPUTATION (e, cl)]
         in
         let body = statements' @ pre_cont @ statements2' @ pre_cond in
         let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = body}, cl) in
         let x' = Cabs.WHILE (formula, expression_cond0', statement', cl) in
         (map, pre_init @ [x'], cl)
       end
    | Cabs.RETURN (expression, cl) ->
       let (expression', map) = extract_ref_call [] expression in
       let x' = Cabs.RETURN (expression', cl) in
       (map, [x'], cl)
    | Cabs.SWITCH (expression, statement, cl) ->
       let (expression', map) = extract_ref_call [] expression in
       let statements' = extract_statements [statement] in
       let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = statements'}, cl) in
       let x' = Cabs.SWITCH (expression', statement', cl) in
       (map, [x'], cl)
    | Cabs.CASE (expression, statement, cl) ->
       let statements' = extract_statements [statement] in
       let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = statements'}, cl) in
       let x' = Cabs.CASE (expression, statement', cl) in
       ([], [x'], cl)
    | Cabs.CASERANGE (expression1, expression2, statement, cl) ->
       let statements' = extract_statements [statement] in
       let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = statements'}, cl) in
       let x' = Cabs.CASERANGE (expression1, expression2, statement', cl) in
       ([], [x'], cl)
    | Cabs.DEFAULT (statement, cl) ->
       let statements' = extract_statements [statement] in
       let statement' = Cabs.BLOCK ({Cabs.blabels = []; battrs = []; bstmts = statements'}, cl) in
       let x' = Cabs.DEFAULT (statement', cl) in
       ([], [x'], cl)
    | x -> ([], [x], dl)

  and extract_definition definition =
    let dl = {Cabs.lineno = 0;filename = "";byteno = 0;ident = 0;} in
    match definition with
    | Cabs.DECDEF ((specifier, l_init_name), cl) ->
       let (map, l_init_name') =
         (fun (map, l_init_name') (name, init_exp) ->
           let (init_exp', map') = extract_ref_call_init_name map init_exp in
           let init_name' = (name, init_exp') in
           (map', l_init_name' @ [init_name'])
         ) |->> (([],[]), l_init_name) in
       let x' = Cabs.DECDEF ((specifier, l_init_name'), cl) in
       (map, x', cl)
    | x -> ([], x, dl)

  and extract_statements = function
    | [] -> []
    | x::xs ->
       let (map, x', cl) = extract_statement x in
       let pre = get_assignments_cabs cl map in
       pre @ x' @ extract_statements xs
