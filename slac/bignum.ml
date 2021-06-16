(*
==========================
 Bignums
==========================
*)

type t = bool * int list
(* (true,[10;999;123;445]) means 10,999,123,445 (each elem max:1000) *)
(* (false,[10;999;123;445]) means -10,999,123,445 *)

let getSg (bn:t) = fst bn
;;

let getBody (bn:t) = snd bn
;;

let to_string (bn : t) =
  match bn with
  | (_,[]) -> ""
  | (sg,n::bn') ->
     let _res = ref (string_of_int n) in
     for i = 0 to List.length bn' - 1 do
       let s = string_of_int (List.nth bn' i) in
       let s' =
         match Bytes.length s with
         | n when n > 3 -> failwith "Bignum.to_string: unexpected input"
         | n -> (Bytes.make (3-n) '0') ^ s
       in
       _res := !_res ^ s'
     done;
     let sg' = if sg then "" else "-" in
     sg' ^ !_res
;;

let of_string (str : bytes) : t =
  (* This may return "Failure _" exception if str is not a numeral string *)    
  if str = "" then (true,[]) else
    (* eliminating parenthese *)
    let str = if Bytes.get str 0 = '(' then (Bytes.sub str 1 (Bytes.length str - 2)) else str in 
    let sg = if Bytes.get str 0 <> '-' then true else false in
    let str' = if sg then str else Bytes.sub str 2 (Bytes.length str - 2) in
    let _t = ref "" in
    let _res = ref [] in
    for i = 0 to Bytes.length str' - 1 do
      let pos = Bytes.length str' - i - 1 in
      let s = Bytes.sub str' pos 1 in
      _t := s ^ !_t;
      if i mod 3 == 2
      then
        begin
          _res := !_t :: !_res;
          _t := ""
        end
      else ();
    done;
    if !_t <> "" then _res := !_t :: !_res;
    (sg,List.map int_of_string !_res)
;;

let println bn = print_endline (to_string bn)
;;

let to_int (bn : t) = (* when bn is a small integer *)
  let (sg,nn) = bn in
  let rec aux res nn1 =
    match nn1 with
    | [] -> res
    | n::nn' -> aux (1000*res+n) nn'
  in
  let num = aux 0 nn in
  if sg
  then num
  else (-1) * num
;;

let of_int n : t =
  let (sg,n') = if n >= 0 then (true,n) else (false,(-1)*n) in
  let _bn = ref [] in
  let _n = ref n' in
  while !_n <> 0 do
    _bn := (!_n mod 1000) :: !_bn;
    _n := !_n / 1000
  done;
  (sg,!_bn)
;;

let compare (bn1 : t) (bn2 : t) =
  let (sg1,nn1) = bn1 in
  let (sg2,nn2) = bn2 in
  let rec compare_same nn1 nn2 =
    match nn1, nn2 with
    | [],[] -> 0
    | n1::nn1',n2::nn2' when n1 < n2 -> -1
    | n1::nn1',n2::nn2' when n1 > n2 -> 1
    | _::nn1',_::nn2' -> compare_same nn1' nn2'
    | _,_ -> failwith "Bignum.compare: unexpected input"
  in
  let len1 = List.length nn1 in
  let len2 = List.length nn2 in
  if len1 > len2 || sg1 > sg2 then 1
  else if len1 < len2 || sg1 < sg2 then -1
  else compare_same nn1 nn2
;;


