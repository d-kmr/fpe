(*--------------------------------------------*)
(* Tools				*)
(*--------------------------------------------*)
exception Error of string;;
exception EXCEPT of string;;
exception Succeed;;
exception Fail;;
exception UNKNOWN;;
exception Skip;;
exception Break;;
exception NotWhite;;


module V = Map.Make(Bytes);;
         
let fst3 (x,_,_) = x;;
let snd3 (_,y,_) = y;;
let thd3 (_,_,z) = z;;

let fst4 (x,_,_,_) = x;;
let snd4 (_,y,_,_) = y;;
let thd4 (_,_,z,_) = z;;
let fth4 (_,_,_,w) = w;;

let print_string' str = print_string str; flush_all()

(*
let print_string = prerr_string;;
let print_endline = printr_endline;;
 *)

(*
let print_warn tag mes = print_endline @@ "[W " ^ tag ^ "] " ^ mes

let print_error tag mes = print_endline @@ "[E " ^ tag ^ "] " ^ mes

let print_mes tag mes = print_endline @@ "[_ " ^ tag ^ "] " ^ mes
 *)

let size_of_list sz_one (someL: 'a list) = List.fold_left (fun n x -> n + sz_one x) 0 someL
;;                        
let size_of_bytesL ss = size_of_list Bytes.length ss
;;                      
let size_of_v sz_key sz_node (someV: 'a V.t) = V.fold (fun key node m -> m + (sz_key key) + (sz_node node)) someV 0
;;
                        
let myOrdinal n =
  let th = 
    if n = 11 || n = 12 then "-th"
    else
      match n mod 10 with
      | 1 -> "st"
      | 2 -> "nd"
      | 3 -> "rd"
      | _ -> "-th"
  in
  (string_of_int n) ^ th

let order1 v1 v2 = if v1 > v2 then 1 else if v1 < v2 then -1 else 0
;;
let order2 (v1,_) (v2,_) = order1 v1 v2
;;
let order3 (v1,_,_) (v2,_,_) = order1 v1 v2
;;
let order4 (v1,_,_,_) (v2,_,_,_) = order1 v1 v2
;;
let rec sum ls = if ls = [] then 0 else List.hd ls + sum (List.tl ls)
;;
let rec maxlist ls = List.fold_right max ls 0
;;
let setminus ls1 ls2 = List.filter (fun x -> not(List.mem x ls2)) ls1
;;
let intersectL ll =
  let module L = List in
  if ll = [] then [] else
	let _res = ref (L.hd ll) in
	let _ll = ref (L.tl ll) in
	while !_res <> [] && !_ll <> [] do
	  _res := L.filter (fun x -> L.mem x (L.hd !_ll)) !_res;
	  _ll := L.tl !_ll;
	done;
	!_res
;;	  
let intersect l1 l2 = intersectL [l1;l2]
;;	
let subset ls1 ls2 = setminus ls1 ls2 = []
;;
let seteq ls1 ls2 = (subset ls1 ls2) && (subset ls2 ls1)
;;
let disjoint ls1 ls2 = intersect ls1 ls2 = []
;;
let rec union ls1 ls2 =
  match ls2 with
  | [] -> ls1
  | x::ls2' ->
     if List.mem x ls1
     then union ls1 ls2'
	 else union (x::ls1) ls2'
;;
let unionL (ll: 'a list list) : 'a list = List.fold_left (fun ls1 ls2 -> union ls1 ls2 ) [] ll
;;

let eqList eq ls1 ls2 =
  let rec eqListOne a lsCheck =
    match lsCheck with
    | [] -> raise Fail
    | (x,b) :: lsCheck1 when b = true && eq x a -> (x,false)::lsCheck1
    | hd :: lsCheck1 -> hd :: (eqListOne a lsCheck1)
  in
  let len1 = List.length ls1 in
  let len2 = List.length ls2 in
  try
    if len1 <> len2 then raise Fail else
    let _ls2 = ref (List.map (fun x -> (x,true)) ls2) in      
    List.iter (fun a -> _ls2 := eqListOne a !_ls2) ls1;
    true
  with
  | Fail -> false
;;

let eqList1 eq ls1 ls2 = eqList eq ls1 ls2
;;
let eqList2 eq lls1 lls2 = eqList (eqList1 eq) lls1 lls2
;;


let rec findOption cond ls =
  match ls with
  | [] -> None
  | hd::tail -> if cond hd then (Some hd) else findOption cond tail;;

let findPosOption x ls = 
  let rec findPosRec x' ls' n = match ls' with
  | [] -> None
  | hd::tail -> if x' = hd then Some n else findPosRec x' tail (n+1)
  in findPosRec x ls 0;;

let findItemOption key ls =
  try
    let itm = List.assoc key ls in
    Some itm
  with
    Not_found -> None
;;

let findItemOptionV key vV = 
  try
    let itm = V.find key vV in
    Some itm
  with
    Not_found -> None
;;

let dropRed ls = List.fold_left (fun ls x -> if List.mem x ls then ls else x::ls) [] ls
;;  

let dropRedSorted equal ls =
  let rec dropRedSortedRec cur res =
    match cur with
    | [] -> List.rev res
    | x::cur' ->
       match res with
       | [] -> dropRedSortedRec cur' [x]
       | y::res' -> if equal x y then dropRedSortedRec cur' res
		    else dropRedSortedRec cur' (x::res)
  in dropRedSortedRec ls [];;
    
let isSubList ls1 ls2 = 
List.fold_right (fun x b -> (List.mem x ls2)&& b) ls1 true;;

let rec isSubListSorted order ls1 ls2 = match ls1,ls2 with
  | [], _ -> true
  | x::ls1', y::ls2' ->
     if order x y = 0 then isSubListSorted order ls1' ls2
     else if order x y > 0 then isSubListSorted order ls1 ls2'
     else false
  | _, _ -> false
					     
  
let countElemLst x lst = 
  let rec countElemLstRec y ls n = match ls with
    | [] -> n
    | hd::tail -> if y = hd then countElemLstRec y tail (n+1)
		  else countElemLstRec y tail n
  in countElemLstRec x lst 0;;

let isLinearList x ls = 
  let n = countElemLst x ls in
  if n = 1 then true else false;;
  
let rec elimElemLst x lst = match lst with
  | [] -> []
  | hd::tail -> if x = hd then elimElemLst x tail else hd::(elimElemLst x tail);;

let rec elimElemLstL xlst lst = match xlst with
  | [] -> lst
  | x::xlst' -> elimElemLstL xlst' (elimElemLst x lst);;

let interLst ls1 ls2 = 
  let rec interLstRec lst1 lst2 rest = match lst2 with
  | [] -> rest
  | x::xl -> if List.mem x lst1 then interLstRec lst1 xl (x::rest) 
	else interLstRec lst1 xl rest
  in List.rev(interLstRec ls1 ls2 []);;

(* zipLst [1;2;3] [a;b;c] is [(1,a);(2,b);(3,c)]*)
let rec zipLst ls1 ls2 = 
  match ls1,ls2 with
  | (hd1::tl1,hd2::tl2) -> (hd1,hd2)::(zipLst tl1 tl2)
  | (_,_) -> [];;

let rec zipLst3 ls1 ls2 ls3 =
  match ls1,ls2,ls3 with
  | (hd1::tl1,hd2::tl2,hd3::tl3) -> (hd1,hd2,hd3)::(zipLst3 tl1 tl2 tl3)
  | (_,_,_) -> [];;
  
(* genLst 3 is [2;1;0] *)
let rec genLst n = if n = 0 then [] else (n-1)::(genLst (n-1));;

let genLstAB n m =
  let _res = ref [] in
  for i = n to m do
    _res := i :: !_res;
  done;
  List.rev !_res
;;

let putIndexes ls =
  let len = List.length ls in
  let idxL = List.rev (genLst len) in
  zipLst ls idxL
;;

let rec genNumLL n len = if len = 0 then [[]] else 
     let res = genNumLL n (len-1) in
     let lstN = List.rev (genLst n) in
     let addHd n = List.map (fun l->n::l) res in
     List.concat (List.map (fun x-> addHd x) lstN);;

let rec genNbools len = 
  let i2b n = if n = 0 then false else true in
  let iL2bL ls = List.map i2b ls in
  List.map iL2bL (genNumLL 2 len);;

let rec genNtrues len = 
  let i2b n = true in
  let iL2bL ls = List.map i2b ls in
  List.map iL2bL (genNumLL 1 len);;

let rec allTrueMes cond lst = 
	match lst with
	| [] -> None
	| hd::tail -> if cond hd then allTrueMes cond tail 
		        else Some hd;;

let allTrue cond lst : bool = match allTrueMes cond lst with
  | None -> true
  | Some _ -> false;;

let put_index_to_list ls =
  let n = List.length ls in
  let indexL = List.rev (genLst n) in
  zipLst indexL ls

(* makeCombPairs [1;2;3] returns [(1,2);(1,3);(2,3)]	*)
let rec makeCombPairs ls = match ls with
  | [] -> []
  | hd::tail -> 
     let ls1 = List.map (fun x-> (hd,x)) tail in
     let ls2 = makeCombPairs tail in
     List.append ls1 ls2;;

(* makeCombPairs2 [1;2] ['A';'B']returns [(1,'A');(1,'B');(2,'A');(2,'B')]*)
let rec makeCombPairs2 ls1 ls2 = 
  let makeCP1 ls x = List.map (fun v -> (v,x)) ls in
  List.concat (List.map (makeCP1 ls1) ls2);;

let makeDiffPairs ls = 
  let rec makeDiffPairRec lst x = match lst with
    | [] -> []
    | y::yL -> let rest = makeDiffPairRec yL x in
	        if x = y then rest else (x,y)::rest
  in
  List.concat(List.map (makeDiffPairRec ls) ls);;

(* Generating Fresh Variables *)
let genFreshVar sym vlst =   
  let rec genFreshVarRec s l n =
    let newVar = s^(string_of_int n) in
    if List.mem newVar l then genFreshVarRec s l (n+1) 
    else newVar
  in genFreshVarRec sym vlst 0;;

let rec genFreshVarL sym lst len = 
	if len = 0 then [] else
	let v = genFreshVar sym lst in
	v::(genFreshVarL sym (v::lst) (len-1));;

let string_of_list (f: 'a -> string) sepsym strL = 
	List.fold_right 
	(fun x y -> if y = "" then f x else (f x)^sepsym^y)
	strL ""
;;

let string_of_V (f: bytes -> 'a -> string) sepsym strV = 
	V.fold
	(fun k x y -> if y = "" then f k x else (f k x)^sepsym^y)
	strV ""
;;

let string_of_V' (f: 'a -> string) sepsym strV =
  let f' key x = f x in
  string_of_V f' sepsym strV
;;

let print_list (pp: 'a -> unit) sepsym ls =
  match ls with
  | [] -> ()
  | x::xl ->
     pp x;
     List.iter
       (fun y -> print_string' sepsym; pp y)
       xl
;;

let println_list pp sepsym ls =
  print_list pp sepsym ls;
  print_endline ""
;;

let println_list' pp sepsym ls =
  match ls with
  | [] -> ()
  | _ ->
     print_list pp sepsym ls;
     print_endline ""
;;


let print_V (pp: bytes -> 'a -> unit) sepsym strV =
  V.fold
    (fun key d _ -> pp key d; print_string' sepsym)
    strV
    ()
;;

(* from 4.03 this is supported
let unionV (f : bytes -> 'a -> 'a -> 'a option) strV1 strV2 =
  let f' key opt1 opt2 =
    match opt1,opt2 with
    | None,_ -> opt2
    | _,None -> opt1
    | Some v1,Some v2 -> f key v1 v2
  in
  V.merge f' strV1 strV2
;;
 *)

(* from 4.05 this is supported
let find_optV key strV =
  try
    Some (V.find key strV)
  with
    Not_found -> None
;;
 *)

(* from 4.03 this is supported
(* update works if the given key exists *)
let updateV key (f: ('a option -> 'a option)) strV =
  match find_optV key strV with
  | None -> strV
  | Some v ->
     match f (Some v) with
     | None -> V.remove key strV
     | Some w -> V.add key w (V.remove key strV)
;;
 *)

(* added the key if it does not exist *)
let updateV' key (f: ('a option -> 'a option)) strV =
  match V.find_opt key strV with
  | None ->
     begin
       match (f None) with
       | None -> strV
       | Some w -> V.add key w strV
     end
  | Some v ->
     begin
       match f (Some v) with
       | None -> V.remove key strV
       | Some w -> V.add key w (V.remove key strV)
     end
;;

(* replace by string_of_list
let rec mapSymbol (f: 'a -> string) sepsym basesym strL = match strL with
   | [] -> basesym
   | [x] -> f x
   | x::xl -> (f x)^sepsym^(mapSymbol f sepsym basesym xl);;
*)
(* replace by string_of_list
let rec concatStr s ls = match ls with
  | [] -> ""
  | [x] -> x
  | x::xl -> x^s^(concatStr s xl);;
*)

(*let mapComma f strL = mapSymbol f (", ") ("") strL;;*)
let mapComma f strL = string_of_list f (", ") strL;;

let concatStrLComma = mapComma (fun s -> s);;

(*let mapNewLine f strL = mapSymbol f ("\n") ("") strL;;*)
let mapNewLine f strL = string_of_list f ("\n") strL;;

let concatStrLNewLine = mapNewLine (fun s -> s);;

let rec replLstNth n e ls = match ls with
  | [] -> []
  | hd::tl -> if n = 0 then e::tl else hd::(replLstNth (n-1) e tl);;

let permute_optlist (ols : 'a option list) : 'a list option = 
	if List.exists (fun x-> x = None) ols then None else
	  let ll = List.map (fun x -> match x with None -> [] | Some y -> [y]) ols in
	Some (List.concat ll);;

let func_option f (opt : 'a option) : 'b option = match opt with
  | None -> None
  | Some a -> Some (f a);;

let getPos v lst = 
  let rec getPosRec x l n result = match l with
    | [] -> result
    | hd::tl -> 
	if x = hd then getPosRec x tl (n+1) (n::result) 
	else getPosRec x tl (n+1) result
  in List.rev (getPosRec v lst 0 []);;

let rec isLinear lst = match lst with
  | [] -> true
  | x::xl -> if List.mem x xl then false else isLinear xl;;

let rec isLinearSorted ls = match ls with
  | [] -> true
  | x::ls' -> match ls' with
	      | [] -> true
	      | y::ls'' -> if x = y then false else isLinearSorted ls';;
  
(* occurLst ["a";"b";"b";"b"] returns ["a0";"b0";"b1";"b2"]  *)
let occurLst1 ls = 
    let rec occurLstRec ls rest memo = 
      match rest with
      | [] -> ls
      | x::xl -> 
	 let n = countElemLst x memo in
	 occurLstRec (ls@[(x,n)]) xl (x::memo)
    in occurLstRec [] ls [];;

let occurLst ls = List.map (fun (x,n)->x^(string_of_int n)) (occurLst1 ls);;

(* gatherKey2 [(1,"a","A");(2,"b","B");(1,"c","C");(1,"d","D")] returns [("a","A");("c","C");("d","D")]  *)
let gatherKey2 ls key = 
  let rec gatherKeyRec ls ky rest = match rest with
    | [] -> ls
    | (k,x,y)::xl -> if k = ky then gatherKeyRec (ls@[(x,y)]) ky xl else gatherKeyRec ls ky xl
  in gatherKeyRec [] key ls;;
  
let memEq eq x ls = List.exists (eq x) ls;;

let sublistEq eq ls1 ls2 = List.for_all (fun x -> memEq eq x ls2) ls1;;

let eqlistEq eq ls1 ls2 = (sublistEq eq ls1 ls2) && (sublistEq eq ls2 ls1);;

let strhd str = String.get str 0;;

let strtl str = 
  let len = String.length str in
  String.sub str 1 (len-1);;

let rec lexorder (ord : 'a -> 'a -> int) ls1 ls2 = 
  match (ls1, ls2) with
  | ([],[]) -> 0
  | (_,[]) -> 1
  | ([],_) -> -1
  | (_,_) -> 
       if ord (List.hd ls1) (List.hd ls2) > 0 then 1 
       else if ord (List.hd ls1) (List.hd ls2) < 0 then -1
       else lexorder ord (List.tl ls1) (List.tl ls2) ;;

let rec toCharList s = 
  let len = String.length s in
  if len = 0 then [] else 
  let hd = String.get s 0 in
  let tl = String.sub s 1 (len - 1) in
  hd::(toCharList tl);;

let strlexorder s1 s2 = 
  let chorder c1 c2 = if c1 > c2 then 1 else if c1 < c2 then -1 else 0 in
  let s1' = toCharList s1 in
  let s2' = toCharList s2 in
  lexorder chorder s1' s2';;

(* mergeL (>) [[1;4;7];[2;5;8];[3;6;9]] returns [1;2;3;4;5;6;7;8;9]*)
let mergeL order = List.fold_left (fun l l' -> List.merge order l l') [];;

let mkEqClass elems eql = 
  let n = List.length elems in
  let numL = List.rev (genLst n) in
  let table = ref (zipLst elems numL) in
  let gatherElemIndex n = 
    let lst = List.filter (fun (x,i) -> i = n) !table in
    List.map (fun (x,_) -> x) lst 
  in 
  let rec updateIndexRec i j tbl rest = match tbl with
    | [] -> List.rev rest
    | (e,k)::tbl' -> if i = k then updateIndexRec i j tbl' ((e,j)::rest)
		     else updateIndexRec i j tbl' ((e,k)::rest)
  in 
  let updateIndex i j = table := updateIndexRec i j !table [] in
  let updateTable (a,b) = 
    let idxa = List.assoc a !table in
    let idxb = List.assoc b !table in
    let min, max = min idxa idxb, max idxa idxb in
    updateIndex max min 
  in 
  List.iter updateTable eql;
  List.filter (fun ls -> ls <> []) (List.map gatherElemIndex numL);;

let rec findClass clsL e = match clsL with
  | [] -> []
  | ls::clsL' -> if List.mem e ls then ls else findClass clsL' e;;

let mkClosure clsL eL =
  let rec mkClos1 rest elst = match elst with
    | [] -> rest
    | e::elst' ->
       mkClos1 (e::(findClass clsL e)@rest) elst'
  in dropRed (mkClos1 [] eL);;

let disjoint ls1 ls2 =
  let answer = ref true in
  begin
	try
	  for i = 0 to List.length ls1 - 1 do
		if List.mem (List.nth ls1 i) ls2 then raise Break else ()
	  done;
	with
	  Break -> answer := false
  end;
  !answer
(*
let setminus ls1 ls2 = List.filter (fun x -> not(List.mem x ls2)) ls1

let intersectL ll =
  let module L = List in
  if ll = [] then [] else
	let _res = ref (L.hd ll) in
	let _ll = ref (L.tl ll) in
	while !_res <> [] && !_ll <> [] do
	  _res := L.filter (fun x -> L.mem x (L.hd !_ll)) !_res;
	  _ll := L.tl !_ll;
	done;
	!_res
	  
let intersect l1 l2 = intersectL [l1;l2]
	
let subset ls1 ls2 = setminus ls1 ls2 = []

let seteq ls1 ls2 = (subset ls1 ls2) && (subset ls2 ls1)

let disjoint ls1 ls2 = intersect ls1 ls2 = []
                                           *)
                     
let cut_string (sym: char) str =
  (* sym is a separator *)
  let str' = str ^ (Bytes.make 1 sym) in (* put sentinel *)
  let len = Bytes.length str' in
  let _res = ref [] in
  let _pos = ref 0 in
  for i = 0 to len - 1 do
    if Bytes.get str' i = sym then
      begin
        _res := (Bytes.sub str' !_pos (i - !_pos)) :: !_res;
        _pos := i + 1;
      end
    else ()
  done;
  List.rev !_res
;;

let cut_string2 (sym: bytes) str =
  let max = Bytes.length str in
  let isMatchIndex curIdx =
    if max < curIdx + (Bytes.length sym) then false
    else Bytes.sub str curIdx (Bytes.length sym) = sym
  in
  let rec findNextMatchIndex curIdx =
    match max < curIdx + (Bytes.length sym), isMatchIndex curIdx with
    | true,_ -> None
    | _,true -> Some curIdx
    | _,_ -> findNextMatchIndex (curIdx+1)
  in
  let rec aux res curIdx =
    match findNextMatchIndex curIdx with
    | None -> res @ [Bytes.sub str curIdx (max-curIdx)]
    | Some nextIdx ->
       aux (res @ [Bytes.sub str curIdx (nextIdx-curIdx)]) (nextIdx+(Bytes.length sym))
  in
  aux [] 0
;;      
  
(* Simple Equality Check *)
(* simpleEqCheck [(a,b);(b,c);(c,d)] (a,d) checks a=b,b=c,c=d |= a=d *)
let simpleEqCheck eqs eq =
  let replace sub e3 =
    let (e1,e2) = sub in
    if e1 = e3 then e2 else e3
  in
  let update sub (e1,e2) = (replace sub e1, replace sub e2) in
  let rec aux eqs0 =
    match eqs0 with
    | [] -> false
    | [(e1,e2)] when e1 = e2 -> true
    | (e1,e2)::eqs1 ->
       let eqs1' = List.map (update (e1,e2)) eqs1 in
       aux eqs1'
  in
  aux (eqs @ [eq])
;;  

(* transClos [[1;2];[2;3];[4;5];[5;6];[7;7]] computes the transitive closure of the input *)
(* that is, it returns [[7; 7]; [4; 5; 6]; [1; 2; 3]] *)
(* Note that the input is considered as a ref.sym.relation. *)
(* So transClos returns the smallest eq.rel. that contains it *)
let transClos xll =
  let rec f xl yll zll =
    match zll with
    | [] -> (xl,List.rev yll)
    | zl::zll' when intersect xl zl = [] -> f xl (zl::yll) zll'
    | zl::zll' ->
       let xl' = union xl zl in
       let zll' = (List.rev yll) @ zll' in
       f xl' [] zll'
  in
  let res = ref [] in
  let cur = ref (List.filter (fun xl -> xl <> []) xll) in
  while !cur <> [] do
    let (xl,yll) = f (List.hd !cur) [] (List.tl !cur) in
    res := xl :: !res;
    cur := yll;
  done;
  !res
;;

let genExp n =
  let rec aux res k = 
    match k with
    | 0 -> res
    | _ ->
       let res0 = List.map (fun l -> false::l) res in
       let res1 = List.map (fun l -> true::l) res in
       aux (res1@res0) (k-1)
  in
  aux [[]] n
;;

(* updateList [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateList [("x",1);("z",2)] "y" 5 returns [("x",1);("z",2);("y",5)] *)
let updateListFlag ls x u =
  let _updateflag = ref false in  
  let rec aux res ls0 =
    match ls0 with
    | [] ->
       _updateflag := true;
       List.rev_append res [(x,u)]
    | (y,v)::ls1 when x = y && v = u ->
       List.rev_append res ((y,v)::ls1)
    | (y,v)::ls1 when x = y  ->
       _updateflag := true;       
       List.rev_append res ((x,u)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  (aux [] ls,!_updateflag)
;;

let updateList ls x u = fst (updateListFlag ls x u)
;;

(* updateList_strict [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateList_strict [("x",1);("z",2)] "y" 5 fails *)
let updateList_strict ls x u =
  let rec aux res ls0 =
    match ls0 with
    | [] -> raise Not_found
    | (y,_)::ls1 when x = y -> List.rev_append res ((x,u)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  aux [] ls
;;       

(* updateList3 [("x",1,u);("y",2,v)] "y" 5 w returns [("x",1,u);("y",5,w)] *)
(* updateList3 [("x",1,u);("z",2,v)] "y" 5 w returns [("x",1,u);("z",2,v);("y",5,w)] *)
let updateList3 ls x u1 u2 =
  let rec aux res ls0 =
    match ls0 with
    | [] -> List.rev_append res [(x,u1,u2)]
    | (y,_,_)::ls1 when x = y -> List.rev_append res ((x,u1,u2)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  aux [] ls
;;

(* updateList_strict [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateList_strict [("x",1);("z",2)] "y" 5 fails *)
let updateList3_strict ls x u1 u2 =
  let rec aux res ls0 =
    match ls0 with
    | [] -> raise Not_found
    | (y,_,_)::ls1 when x = y -> List.rev_append res ((x,u1,u2)::ls1)
    | hd::ls1 -> aux (hd::res) ls1
  in
  aux [] ls
;;       


(* updateListOrder [("x",1);("y",2)] "y" 5 returns [("x",1);("y",5)] *)
(* updateListOrder [("x",1);("z",2)] "y" 5 returns [("x",1);("y",5);("z",2)] *)
let updateListOrderFlag order ls x u =
  let _updateflag = ref false in
  let rec aux res ls0 =
    match ls0 with
    | [] ->
       _updateflag := true;
       List.rev_append res [(x,u)]
    | (y,v)::ls1 when order x y > 0 -> aux ((y,v)::res) ls1
    | (y,v)::ls1 when order x y < 0 ->
       _updateflag := true;
       List.rev_append ((y,v)::(x,u)::res) ls1
    | (_,v)::ls1 when u<>v ->
       _updateflag := true;         
       List.rev_append ((x,u)::res) ls1
    | (_,v)::ls1 ->
       List.rev_append ((x,u)::res) ls1
  in
  (aux [] ls,!_updateflag)
;;       

let updateListOrder order ls x u = fst (updateListOrderFlag order ls x u)
;;       


(* list_assoc3 [(n0,a0,b0);(n1,a1,b1);(n2,a2,b2)] n2 is (a2,b2) *)
let list_assoc3 key ll =
  let rec aux res ls =
    match ls with
    | [] -> raise Not_found
    | (k,a,b)::ls1 when k = key -> (a,b)
    | c :: ls1 -> aux (c::res) ls1
  in
  aux [] ll
;;  

    
                



module List_tailrec = struct

  let rec rev1 res ls = match ls with
    | [] -> res
    | x::ls' -> rev1 (x::res) ls'

  let rev ls = rev1 [] ls 

  let rec append_rev ls1 ls2 = 
    match ls1 with 
    | [] -> ls2
    | x::ls1 -> append_rev ls1 (x::ls2)

  let append ls1 ls2 = 
    let ls1rev = rev ls1 in
    append_rev ls1rev ls2

  let rec map_rev1 f ls result = match ls with
    | [] -> result
    | x::xl -> map_rev1 f xl ((f x)::result)

  let map_rev f ls = map_rev1 f ls []

  let map f ls = rev (map_rev f ls)

  let rec concat_rev1 res ll = match ll with
    | [] -> res
    | hdL::ll' ->
       let res' = append_rev hdL res in
       concat_rev1 res' ll'

  let concat_rev ll = concat_rev1 [] ll

  let concat ll = rev (concat_rev ll)

  (* allChoice [[1;2];[3;4];[5;6]] returns *)
  (* [1;3;5];[1;3;6];[1;4;5];[1;4;6]	*)
  (* [2;3;5];[2;3;6];[2;4;5];[2;4;6]	*)
  let rec allChoice1 resll ll = match ll with
    | [] -> map rev resll
    | hdL::ll' ->
       let resll' = concat (map (fun i -> map (fun rl -> i::rl) resll) hdL) in
       allChoice1 resll' ll'

  let allChoice ll = allChoice1 [[]] ll


  let rec allChoiceBool1 res ll =
    match ll with
    | [] -> map (fun (b,l) -> (b,rev l)) res
    | (ls1,ls2)::ll' ->
       let res1 = concat (map_rev (fun x-> (map_rev (fun (b,l) -> (b,x::l)) res)) ls1) in
       let res2 = concat (map (fun x-> (map (fun (b,l) -> (true,x::l)) res)) ls2) in
       let res' = append_rev res1 res2 in
       allChoiceBool1 res' ll'

  let allChoiceBool ll = allChoiceBool1 [(false,[])] ll

  (* allChoiceTwo [([1;2],[3;4]);([5;6],[7;8])] returns lists	*)
  (* similar to the result of allChoice [[1;2;3;4];[5;6;7;8]],	*)
  (* except for the choices from [1;2] and [5;6]			*)
  (* That is, it returns						*)
  (* [1;7];[1;8];[2;7];[2;8];					*)
  (* [3;5];[3;6];[3;7];[3;8];[4;5];[4;6];[4;7];[4;8];		*)
  let allChoiceTwo ll =
    let llb = allChoiceBool ll in
    List.fold_left (fun xll (b,l) -> if b then l::xll else xll) [] llb;;

  (* dropsame order ls1 ls2 returns a sublist of ls1, which is obtained by dropping the elements in ls2 *)
  (* ls1 and ls2 are assumed to be sorted w.r.t. order *)
  let rec dropsame1 order res ls1 ls2 = match ls1,ls2 with
	| [],_ -> rev res
	| a::ls1',b::ls2' ->
	   if order a b < 0 then dropsame1 order (a::res) ls1' ls2
	   else if order a b = 0 then dropsame1 order res ls1' ls2
	   else dropsame1 order res ls1 ls2'
	| _,[] -> append_rev res ls1

  let dropsame order ls1 ls2 = dropsame1 order [] ls1 ls2

  let takeNth ls i = 
    let rec takeNthRec res lst pos =
      if lst = [] then failwith "takeNth" else 
        let hd = List.hd lst in
        let tl = List.tl lst in
        match pos with
        | 0 -> (hd, List.rev_append res tl)
        | _ -> takeNthRec (hd::res) tl (pos-1)
    in takeNthRec [] ls i

  let splitNth ls pos =
    let rec aux res ls j =
      match ls,j<pos with
      | [],_ -> (List.rev res,[],[])
      | x::xl,true -> aux (x::res) xl (j+1)
      | x::xl,_ -> (List.rev res,[x],xl)
    in
    aux [] ls 0
    
  let dropNth ls i = let (_,res) = takeNth ls i in res

  let replaceNth ls i a =
    let rec replaceNthRec res lst pos =
      if lst = [] then failwith "replaceNth" else
        let hd = List.hd lst in
        let tl = List.tl lst in
        match pos with
        | 0 -> List.rev_append res (a::tl)
        | _ -> replaceNthRec (hd::res) tl (pos-1)
    in replaceNthRec [] ls i
     
  let rec allChoiceApply1 f chkfunc ll res = match ll with
    | [] -> f(List.rev res)
    | ls::ll' ->
       for i = 1 to List.length ls do
         try
	       allChoiceApply1 f chkfunc ll' (chkfunc ((List.nth ls (i-1))::res))
         with Skip -> ()
       done

  let allChoiceApply f chkfunc ll = allChoiceApply1 f chkfunc ll []

  let permApply f ls =
    let rec permApplyRec res len lst =
      if len = 0 then f res
      else
        for i = 0 to len - 1 do
	      let (x,lst') = takeNth lst i in
	      permApplyRec (x::res) (len-1) lst'
        done
    in
    permApplyRec [] (List.length ls) ls

  let permApply2 f ls1 ls2 =
    permApply (fun ls -> permApply (f ls) ls2) ls1

  (* permApplyL f lls makes all possible permutations of	*)
  (* the lists of lls then apply f to it			*)
  (* e.g. permApplyL f [[1;2];[3;4]] performs		*)
  (* f [[1;2];[3;4]]					*)
  (* f [[1;2];[4;3]]					*)
  (* f [[2;1];[3;4]]					*)
  (* f [[2;1];[4;3]]					*)
  let permApplyL f ll =
    let rec permApplyR rest restl ls lls =
      match ls,lls with
      | [],[] -> f (List.rev ((List.rev rest)::restl))
      | [],ls1::lls1 -> permApplyR [] ((List.rev rest)::restl) ls1 lls1
      | _,_ ->
         for i = 0 to List.length ls - 1 do
	       let (a,ls') = takeNth ls i in
	       permApplyR (a::rest) restl ls' lls
         done
    in
    match ll with
    | [] -> f []
    | ls1::ll1 -> permApplyR [] [] ls1 ll1

  let splitLst filter ls =
    let rec aux lsT lsF ls1 =
      match ls1 with
      | [] -> (List.rev lsT,List.rev lsF)
      | x::ls2 when filter x -> aux (x::lsT) lsF ls2
      | x::ls2 -> aux lsT (x::lsF) ls2
    in
    aux [] [] ls

  (* merge of two assoc lists *)
  let merge (f: 'b -> 'b -> 'b) (assoc1 : ('a * 'b) list) (assoc2 : ('a * 'b) list) : ('a * 'b) list =
    let rec aux res keys =
      match keys with
      | [] -> List.rev res
      | k::keys1 ->
         match List.assoc_opt k assoc1, List.assoc_opt k assoc2 with
         | None,Some x -> aux ((k,x)::res) keys1
         | Some x,None -> aux ((k,x)::res) keys1
         | Some x,Some y -> aux ((k,f x y)::res) keys1
         | None,None -> failwith "List_tailrec.merge"
    in
    let keys1 = List.map fst assoc1 in
    let keys2 = List.map fst assoc2 in
    aux [] (union keys1 keys2)

  (* zip two assoc-list: [(1,a);(2,b)] [(2,c);(3,d)] --> [(1,(a))] *)
  let zip_assoc none assoc1 assoc2 =
    let rec aux res keys =
      match keys with
      | [] -> List.rev res
      | k::keys1 ->
         match List.assoc_opt k assoc1, List.assoc_opt k assoc2 with
         | None,Some x -> aux ((k,(none,x))::res) keys1
         | Some x,None -> aux ((k,(x,none))::res) keys1
         | Some x,Some y -> aux ((k,(x,y))::res) keys1
         | None,None -> failwith "List_tailrec.zip_assoc"
    in
    let keys1 = List.map fst assoc1 in
    let keys2 = List.map fst assoc2 in
    aux [] (union keys1 keys2)
    
end
;;

(* File reader *)
let my_read_file filename =
  let x = ref "" in
  let ic = open_in filename in
  try
	while true do
	  x := !x ^ (input_line ic) ^ "\n"
	done ;
	"" (* dummy *)
  with End_of_file -> close_in ic;!x
;;


module List_mes = struct

  let hd mes ls =
    try
      List.hd ls
    with
      _ ->
      print_endline mes;
      failwith "List_mes.hd"

  let tl mes ls =
    try
      List.tl ls
    with
      _ ->
      print_endline mes;
      failwith "List_mes.tl"
      
  let nth mes ls n =
    try
      List.nth ls n
    with
      _ ->
      print_endline mes;
      failwith "List_mes.nth"

  let nth' mes print_func ls n =
    try
      List.nth ls n
    with
      _ ->
      print_endline @@ "Exception from List_mes.nth'!!";
      print_endline @@ "Mes: " ^ mes;
      print_endline @@ "List: ";
      List.iter print_func ls;
      print_endline @@ "Nth: " ^ (string_of_int n);
      failwith "List_mes.nth"
      
  let assoc mes key ls =
    try
      List.assoc key ls
    with
      _ ->
      print_endline mes;
      failwith "List_mes.assoc"

  let assoc3 mes key ls =
    try
      list_assoc3 key ls
    with
      _ ->
      print_endline mes;
      failwith "List_mes.assoc3"             
      
end
;;

module V_mes = struct

  let find mes key strV =
    try
      V.find key strV
    with
      Not_found ->
      print_endline mes;
      failwith "V_mes.find"

  let dropNone (strOptV: 'a option V.t) : 'a V.t =
    let strV = V.filter (fun _ opt -> match opt with None -> false | Some _ -> true) strOptV in
    V.map (fun opt -> match opt with None -> failwith "" | Some x -> x) strV

  let update key (upfun: 'a option -> 'a option) (strV: 'a V.t) : 'a V.t =
    match V.find_opt key strV with
    | None ->
       begin
         match upfun None with
         | None -> strV
         | Some w -> V.add key w strV
       end
    | Some v ->
       begin
         match upfun (Some v) with
         | None -> V.remove key strV
         | Some w when v = w -> strV
         | Some w -> V.add key w (V.remove key strV)
       end
    
end
;;
