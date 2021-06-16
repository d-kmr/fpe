#load "tools.cmo";;
#load "slsyntax.cmo";;
#load "entlcheck_b.cmo";;
#load "smtsyntax.cmo";;
#load "smttoz3.cmo";;
open Tools;;
open Slsyntax;;
open Entlcheck_b;;
open Smtsyntax;;
open Smttoz3;;

let zero = Exp.Int 0;;
let one = Exp.Int 1;;
let lambda = Exp.Var "lambda";;
let len_ck = Exp.Var "len_ck";;
let n_ck = Exp.Var "n_ck";;
let m_1_lam = Exp.App("*",[one;lambda]);;
let m_n1_lam = Exp.App("*",[Exp.Int (-1);lambda]);;

let all1 =
  (all' ["in_ck";"out_ck";"len_ck";"n_ck";"ivec"]
     (Exp.App("and",
              [
                Exp.App("distinct", [Exp.App("+",[n_ck; m_1_lam]); zero]);
                Exp.App("distinct", [Exp.App("+",[len_ck;m_n1_lam]); zero])
              ]
  )))
;;
let all2 =
  (all' ["in_ck";"out_ck";"len_ck";"n_ck";"ivec"]
     (Exp.App("not",
             [
               Exp.App("and",
                       [
                         Exp.App("distinct",[Exp.App("+",[n_ck;m_1_lam]);zero]);
                         Exp.App("distinct",[Exp.App("+",[len_ck;m_n1_lam]);zero])
                       ]
                 )
             ]
  )))
;;
let e = (all' ["lambda"] (Exp.App("or",[all1;all2])))
;;

(* print e *)
Exp.println e;;

(* checking e *)
checkValidExp e;;
checkSatExp e;;
