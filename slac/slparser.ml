(*----------------------------------------------*)
(* Parser for Separation Logic 			*)
(*----------------------------------------------*)
open Tools;;
open Slsyntax;;

(*----------------------------------------------*)
(* Syntax of Entailments			*)
(*  <atom> ::= x | n | (+ <term>* ) | (<term>)	*)
(*  <term> ::= <atom> + <term> | <atom>		*)
(*  <pexp> ::= <term> = <term>			*)
(*           | <term> =/ <term>			*)
(*           | <term> < <term>			*)
(*           | <term> <= <term>			*)
(*           | (= <term>* )			*)
(*           | (=/ <term>* )			*)
(*           | (< <term>* )			*)
(*           | (<= <term>* )			*)
(*  <pure> ::= <pexp> & .. & <pexp>		*)
(*  <sexp> ::= Emp				*)
(*           | <term> -> (<term>* )		*)
(*           | Array(<term>,<term>)		*)
(*  <spat> ::= <sexp> * .. * <sexp> 		*)
(*  <sh>   ::= <pure> & <spat>			*)
(*  <entl> ::= <sh> |- <sh>			*)
(*----------------------------------------------*)


(*----------------------------------------------*)
(* Tools					*)
(*----------------------------------------------*)
module SLparser = struct

exception ParseError of string

(* Parser Type *)
type 'a parser = string -> ('a * string) option

let stringToCharLst str = 
  let rec stringToCharLstRec s n =
	if n = Bytes.length s then [] else
	(s.[n])::stringToCharLstRec s (n+1)
  in
  stringToCharLstRec str 0

let stringHd (str : string) = str.[0]

let stringTl (str : string) = Bytes.sub str 1 (Bytes.length str - 1)

let charLstToString (chrLst : char list) : string = 
  let len = List.length chrLst in 
  let str = Bytes.create len in 
  let i = ref 0 in 
while !i < len do
	Bytes.set str !i (List.nth chrLst !i); 
	i := !i + 1
done;
str

let charToString (c : char) : string = 
  let str = Bytes.create 1 in 
  Bytes.set str 0 c; 
  str

(* Basic Parsers *)
let allchar : char parser = fun str -> 
  if Bytes.length str = 0 then None
  else Some(stringHd str,stringTl str)

let item : char parser = function
  | "" -> None
  | str -> Some (stringHd str, stringTl str)

let dummy : string parser = fun str -> Some("",str)

(* parse with a parser *)
let parse (p : 'a parser) (str : string) = p str

(* functor *)
let func (f : 'a -> 'b) (p : 'a parser) : 'b parser = 
fun str ->
  match parse p str with
      | None -> None
      | Some (x, res) -> Some (f x, res)

(* combining two parsers *)
let comb (p1 : 'a parser) (p2 : 'b parser) : ('a * 'b) parser = 
fun str -> 
match parse p1 str with
      | None -> None
      | Some (x,res) -> match parse p2 res with 
			| None -> None
			| Some (y, res') -> Some ((x,y), res')

let combLst (pLst : 'a parser list) : 'a list parser = 
  let pairToLst (x, l) = x::l in
  let parserNil = fun str -> Some([],str) in
  List.fold_right (fun x -> fun y -> func pairToLst (comb x y)) pLst parserNil

let rec parserCharLstToString (pLst : char parser list) : string parser = 
  func charLstToString (combLst pLst)

let parserOr (p1 : 'a parser) (p2 : 'a parser) : 'a parser = 
fun str -> 
match parse p1 str with 
| None -> parse p2 str
| Some _ as q -> q

let rec parserOrLst (pLst : 'a parser list) : 'a parser = 
fun str -> 
match pLst with
      | [] -> None
      | p::rest -> parserOr p (parserOrLst rest) str
	
let parser2 (p1:'a parser) (p2:'b parser) : ('a*'b) parser =
  fun str ->
    match parse p1 str with
    | None -> None
    | Some(x,str1) ->
      match parse p2 str1 with
      | None -> None
      | Some(y,rest) -> Some((x,y),rest)

let parser2s p1 p2 sep = 
  let p1_sep = parser2 p1 sep in
  let p1_sep_p2 = parser2 p1_sep p2 in
  func (fun ((x,_),z) -> (x,z)) p1_sep_p2

let parser3s p1 p2 p3 sep =  
  let p12 = parser2s p1 p2 sep in
  let p123 = parser2s p12 p3 sep in
  func (fun ((x,y),z) -> (x,y,z)) p123

let parser4s p1 p2 p3 p4 sep =
  let p12 = parser2s p1 p2 sep in
  let p123 = parser2s p12 p3 sep in
  let p1234 = parser2s p123 p4 sep in
  func (fun (((x,y),z),w) -> (x,y,z,w)) p1234

let parser5s p1 p2 p3 p4 p5 sep =
  let p12 = parser2s p1 p2 sep in
  let p123 = parser2s p12 p3 sep in
  let p1234 = parser2s p123 p4 sep in
  let p12345 = parser2s p1234 p5 sep in  
  func (fun ((((x,y),z),w),v) -> (x,y,z,w,v)) p12345

let parser2s_tl p1 p2 sep = func (fun (x,y)->y) (parser2s p1 p2 sep)

let parser3s_tl p1 p2 p3 sep = 
  func (fun (x,y,z)->(y,z)) (parser3s p1 p2 p3 sep)

let parser4s_tl p1 p2 p3 p4 sep = 
  func (fun (x,y,z,w)->(y,z,w)) (parser4s p1 p2 p3 p4 sep)

let parser5s_tl p1 p2 p3 p4 p5 sep = 
  func (fun (x,y,z,w,v)->(y,z,w,v)) (parser5s p1 p2 p3 p4 p5 sep)

let many n (p : 'a parser) sep : ('a list) parser =
  let tail = func (fun (_,y) -> y) (parser2 sep p) in
  let rec manyTail resLst str = 
    match parse tail str with
    | None -> Some(List.rev resLst, str)
    | Some(res1,str1) -> manyTail (res1::resLst) str1
  in 
  fun str ->
    match parse p str with
    | None -> if n = 0 then Some ([], str) else None
    | Some (res,str1) ->
      match manyTail [] str1 with
      | None -> Some ([res],str1)
      | Some(resL,str2) -> Some(res::resL,str2)

let many0 p = many 0 p dummy

let many1 p = many 1 p dummy

(* look-ahead p checks input string str with p          *)
(* It returns Some("",str) if it is accepted by p       *)
(* Otherwise it returns None                            *)
let lookahead (p : 'a parser) : string parser = fun str ->
  match p str with
  | None -> None
  | Some(_,_) -> Some("",str)

let isNot (p : 'a parser) : string parser = fun str ->
  match p str with
  | None -> Some("",str)
  | Some(_,_) -> None
               
let isSymb (chek : char -> bool) : char parser = fun str ->
  match parse item str with
  | None -> None
  |  Some (x, res) as q -> if chek x then q else None

let isDigit = isSymb (fun ch -> 
			let code = Char.code ch 
			in 48 <= code && code <= 57)

let isLowerAlph = isSymb (fun ch -> 
			let code = Char.code ch 
			in 97 <= code && code <= 122)

let isUpperAlph = isSymb (fun ch -> 
			let code = Char.code ch 
			in 65 <= code && code <= 90)

let isAlph = parserOr isLowerAlph isUpperAlph

let isThisChar c = isSymb (fun ch->ch = c)
  
let isThisString str : string parser = 
  let chLst = stringToCharLst str in
  parserCharLstToString (List.map isThisChar chLst)

let isStrictThisString str =
  let isNextChar = parserOrLst [isDigit;isAlph;isThisChar '_'] in
  let isNotNextChar = isNot isNextChar in
  func fst (comb (isThisString str) (lookahead isNotNextChar))
  
let isNotThisChar c = isSymb (fun ch -> ch <> c)

let isNotThisCharMany1 c = many1 (isNotThisChar c)

let isParenL = isThisChar '('
let isParenR = isThisChar ')'
let isBracketL = isThisChar '<'
let isBracketR = isThisChar '>'
let isSqBracketL = isThisChar '['
let isSqBracketR = isThisChar ']'
let isCurlyBracketL = isThisChar '{'
let isCurlyBracketR = isThisChar '}'
let isSpace = isThisChar ' '
let isTab = isThisChar '\t'
let isNewLine = isThisChar '\n'
let isCarriageReturn = isThisChar '\r'
let isColon = isThisChar ':'
let isSemiColon = isThisChar ';'
let isComma = isThisChar ','
let isPeriod = isThisChar '.'
let isUnderScore = isThisChar '_'
let isPrime = isThisChar '\''
let isAst = isThisChar '*'
let isEqual = isThisChar '='
let isNEqual = isThisString "=/"
let isArrow = isThisString "->"
let isAtmark = isThisChar '@'
let isTilde = isThisChar '~'
let isExclamation = isThisChar '!'
let isQuestion = isThisChar '?'
let isSlash = isThisChar '/'
let isDaller = isThisChar '$'
let isParcent = isThisChar '%'
let isHat = isThisChar '^'
let isAnd = isThisChar '&'
let isPlus = isThisChar '+'
let isMinus = isThisChar '-'
let isHat = isThisChar '^'
let isDblQuote = isThisChar '\"'

let splitByThisSymb sym : string parser =
  let flag = ref 0 in
  let rec splitRec c str =
    match parse (many0 (isNotThisChar c)) str with
    | None -> None (* dummy *)
    | Some(hd1,str1) ->
      if String.length str1 = 0 then Some(hd1,"") else
      match parse (isThisString sym) str1 with
      | Some(_,str2) -> flag := 1; Some(hd1,str2)
      | None ->
	let str3 = stringTl str1 in
	match parse (splitRec c) str3 with
	| None -> None (* dummy *)
	| Some(hd2,str4) -> Some(hd1@[c]@hd2,str4)
  in 
  fun str ->
    if String.length sym = 0 then Some(str,"")
    else
      match parse (splitRec (stringHd sym)) str with
      | None -> None
      | Some(hd,rest) ->
	if !flag = 0 then None else
	let res = charLstToString hd in
	Some(res,rest)

let isCommentBody : unit parser = fun str ->
  match parse (many1 (isNotThisChar '\n')) str with
  | None -> None
  | Some(body,str1) -> Some((),str1)
    
let isIgnoredChar = parserOrLst [isSpace; isTab; isNewLine; isCarriageReturn]

let isComment : unit parser =
  parser2s_tl (isThisString "//") isCommentBody dummy
    
let isIgnored = parserOrLst [func (fun c -> ()) isIgnoredChar; isComment]

let isBlanks = many1 isIgnoredChar

let token (p : 'a parser) : 'a parser = 
fun str ->
match parse (many0 isIgnored) str with
 | None -> None (*unused*)
 | Some (_,str) -> 
	match parse p str with
	 | None -> None
	 | Some (res, str) as q -> q

let ignoreParen1 (p : 'a parser) : 'a parser = fun str -> 
match parse (token isParenL) str with
 | None -> None
 | Some(_,str1) ->
   match parse (token p) str1 with
   | None -> None
   | Some(res,str2) ->
     match parse (token isParenR) str2 with
     | None -> None
     | Some(_,str3) -> Some(res,str3)

let rec ignoreParen (p : 'a parser) : 'a parser = fun str ->
match parse p str with
 | Some(_,_) as q -> q
 | None ->
   match parse (ignoreParen1 p) str with
   | None -> None
   | Some(_,_) as q -> q

(* Recognizing Identifiers or Numbers*)
let isIdentifier0 : string parser = 
  let isIdentHd = parserOrLst[isAlph; isUnderScore] in
  let isIdentSymbTl = parserOrLst[isAlph; isDigit; isUnderScore; isPrime] in
  let isIdentTl = func charLstToString (many0 isIdentSymbTl) in
  func (fun (c,s) -> (charToString c)^s) (comb isIdentHd isIdentTl)
                
let isIdentifier noident : string parser =
  let isNotIdentifier = parserOrLst (List.map isStrictThisString noident) in
  fun str -> 
  match isNotIdentifier str with
  | Some(_,_) -> None
  | None -> isIdentifier0 str

let isNumber : int parser = fun str -> 
 match parse (many1 isDigit) str with
 | None -> None
 | Some(chars,rest) -> 
   let n = int_of_string (List.fold_right (fun x->fun y-> (charToString x)^y) chars "") 
   in Some(n,rest)

(*----------------------------------------------*)
(* Useful functions				*)
(*----------------------------------------------*)
let parser2b p1 p2 = parser2s p1 p2 isBlanks
let parser2b_tl p1 p2 = parser2s_tl p1 p2 isBlanks  

let parser3b p1 p2 p3 = parser3s p1 p2 p3 isBlanks
let parser3b_tl p1 p2 p3 = parser3s_tl p1 p2 p3 isBlanks  

let parser4b p1 p2 p3 p4 = parser4s p1 p2 p3 p4 isBlanks
let parser4b_tl p1 p2 p3 p4 = parser4s_tl p1 p2 p3 p4 isBlanks  

let parser5b p1 p2 p3 p4 p5 = parser5s p1 p2 p3 p4 p5 isBlanks
let parser5b_tl p1 p2 p3 p4 p5 = parser5s_tl p1 p2 p3 p4 p5 isBlanks  

(*----------------------------------------------*)
(* Parser with error message			*)
(*----------------------------------------------*)
let addErrorMes (p : 'a parser)  mes : 'a parser = fun str ->
  match parse p str with
  | Some _ as q -> q
  | None -> raise (ParseError mes)

let sayFail p = fun str ->
  match parse p str with
  | Some _ as q -> q
  | None -> raise (ParseError str)
    
(*----------------------------------------------*)    
(* Error Handling				*)
(*----------------------------------------------*)
let isThisStringErr errinfo str =
  let err_meshd = "Parsing Error: " in
  let mkerrmes m = err_meshd^m in
  let mkErr (str,mes) =
    func
      (fun _ -> raise (ParseError (mkerrmes mes)))
      (token (isThisString str)) in
  let isErrors = List.map mkErr errinfo in
  parserOrLst ((isThisString str)::isErrors)

(*----------------------------------------------*)
(* Parser of S-Exp				*)
(*----------------------------------------------*)
let parserSExp p = fun str ->
  match parse isParenL str with
  | None -> None
  | Some(_,str1) ->
  match parse p str1 with
  | None -> None
  | Some(body,str2) ->
  match parse (token isParenR) str2 with
  | None -> None
  | Some(_,rest) -> Some(body,rest)

(*----------------------------------------------*)
(* Parser of Terms				*)
(*  <atom> ::= x | n | nil			*)
(*	 | '('<unsup>')'			*)
(*  <fact> ::= <atom> ('*' <fact>)*		*)
(*  <clus> ::= <fact> ('-' <clus>)*		*)
(*  <term> ::= <clus> ('+' <term>)*		*)
(*  <unsup> ::= <term> (op <unsup>)*		*)
(*----------------------------------------------*)
let unOps = ["=";"/";"&";"|"]
let noIdents = ["Emp";"Any";"Ex"]
  
let rec isTerm str = 
  let isTerm10 = func snd (parser2s isPlus (token isTerm) dummy) in
  let isTerm1 = many0 (token isTerm10) in
  func (fun (t,ts) -> if ts = [] then t else SHterm.Add (t::ts))
    (parser2s isClus isTerm1 dummy) str    
and isClus str =
  let snd = fun (_,t) -> t in
  let isClus10 = func snd (parser2s isMinus (token isClus) dummy) in
  let isClus1 = many0 (token isClus10) in
  func (fun (t,ts) -> if ts = [] then t else SHterm.Sub (t::ts))
    (parser2s isFact isClus1 dummy) str
and isFact str = 
  let snd = fun (_,t) -> t in
  let isFact10 = func snd (parser2s isAst (token isFact) dummy) in
  let isFact1 = many0 (token isFact10) in
  func
    (fun (t,ts) -> if ts = [] then t else
	let u = List.hd ts in
	match t,u with
	| SHterm.Int n,_ -> SHterm.Mul(n,u)
	| _,SHterm.Int n -> SHterm.Mul(n,t)
	| _,_ -> SHterm.Var "unsupported"
    )
    (parser2s isAtom isFact1 dummy) str
and isAtom str = 
  let isAtom0 = func (fun _ -> SHterm.Int 0) (isThisString "nil") in
  let isAtom1 = func (fun x -> SHterm.Var x) (isIdentifier noIdents) in
  let isAtom2 = func (fun n -> SHterm.Int n) isNumber in
  let isAtom3 = parserSExp (token isUnsup) in
  let isAtom4 =
    let isAtom40 = parser2b isNumber (token isTerm) in
    let isAtom41 = func (fun (n,t) -> SHterm.Mul(n,t)) isAtom40 in
    parserSExp isAtom41
  in 
  parserOrLst [isAtom0;isAtom1;isAtom2;isAtom3;isAtom4] str
and isUnsup str =
  let isUnsuppOp = parserOrLst (List.map isThisString unOps) in
  let isUnsup10 = parser2s isUnsuppOp (token isUnsup) dummy in
  let isUnsup1 = many0 (token isUnsup10) in
  func (fun (t,ts) -> if ts = [] then t else SHterm.Var "Unsupported")
    (parser2s isTerm isUnsup1 dummy) str

(*----------------------------------------------*)
(* Parser of Pure Expressions			*)
(*  <pexp> ::= <term> = <term>			*)
(*           | <term> =/ <term>			*)
(*           | <term> < <term>			*)
(*           | <term> <= <term>			*)
(*           | (= <term>* )			*)
(*           | (=/ <term>* )			*)
(*           | (< <term>* )			*)
(*           | (<= <term>* )			*)
(*----------------------------------------------*)
let isPureExp1 : SHpureExp.t parser =
  let module P = SHpureExp in
  let isNeq' = token (isThisString "=/") in
  let isEq' = token (isThisString "=") in
  let isLe' = token (isThisString "<=") in
  let isLt' = token (isThisString "<") in
  let isTerm' = token isTerm in
  let isEqExp0 = parser3s isTerm isEq' isTerm' dummy in
  let isEqExp = func (fun (t1,_,t2) ->  (P.Eq,[t1;t2])) isEqExp0 in
  let isNeqExp0 = parser3s isTerm isNeq' isTerm' dummy in
  let isNeqExp = func (fun (t1,_,t2) -> (P.Neq,[t1;t2])) isNeqExp0 in
  let isLtExp0 = parser3s isTerm isLt' isTerm' dummy in
  let isLtExp = func (fun (t1,_,t2) -> (P.Lt,[t1;t2])) isLtExp0 in
  let isLeExp0 = parser3s isTerm isLe' isTerm' dummy in
  let isLeExp = func (fun (t1,_,t2) -> (P.Le,[t1;t2])) isLeExp0 in
  let isEqSExp0 = parser2b_tl isEq' (many1 isTerm') in
  let isEqSExp1 = func (fun ts -> (P.Eq,ts)) isEqSExp0 in
  let isEqSExp = parserSExp isEqSExp1 in
  let isNeqSExp0 = parser2b_tl isNeq' (many1 isTerm') in
  let isNeqSExp1 = func (fun ts -> (P.Neq,ts)) isNeqSExp0 in
  let isNeqSExp = parserSExp isNeqSExp1 in
  let isLtSExp0 = parser2b_tl isLt' (many1 isTerm') in
  let isLtSExp1 = func (fun ts -> (P.Lt,ts)) isLtSExp0 in
  let isLtSExp = parserSExp isLtSExp1 in  
  let isLeSExp0 = parser2b_tl isLe' (many1 isTerm') in
  let isLeSExp1 = func (fun ts -> (P.Le,ts)) isLeSExp0 in
  let isLeSExp = parserSExp isLeSExp1 in
  parserOrLst
    [isNeqExp;isEqExp;isLtExp;isLeExp;
     isNeqSExp;isEqSExp;isLtSExp;isLeSExp]

let isPureExp = ignoreParen isPureExp1

(*----------------------------------------------*)
(* Parser of Pure-part				*)
(*  <pure> ::= <pexp> & ... &  <pexp> 		*)
(*----------------------------------------------*)
let isPure : SHpure.t parser =
  let isPureExp' = token isPureExp in
  let isAnd' = token (isThisString "&") in
  func (fun x -> [x]) (many 0 isPureExp' isAnd')

(*----------------------------------------------*)
(* Parser of Spat Expressions			*)    
(*  <sexp> ::= Emp				*)
(*           | <term> -> (<term>* )		*)
(*           | Some				*)
(*----------------------------------------------*)
let isSpatExp : SHspatExp.t parser = 
  let module S = SHspatExp in
  let errmes1 = [("emp","Use \"Emp\"\n")] in
  let errmes2 = [("any","Use \"Any\" \n")] in
  let isEmp = isThisStringErr errmes1 "Emp" in
  let isEmpExp = func (fun _ -> S.Emp) isEmp in
  let isPto' = token (isThisString "->") in
  let isAny = isThisStringErr errmes2 "Any" in
  let isAnyExp = func (fun _ -> S.Any) isAny in
  let isTerm' = token isTerm in
  let isComma' = token isComma in
  let isTerms = parserSExp (many 1 isTerm' isComma') in
  let isTerms' = token isTerms in
  let isPtoExp0 = parser3s isTerm isPto' isTerms' dummy in
  let isPtoExp = func (fun (t,_,ts) -> S.Pto(t,ts)) isPtoExp0 in
  parserOrLst [isEmpExp;isPtoExp;isAnyExp]


(*----------------------------------------------*)
(* Parser of Spatial-part			*)
(*  <spat> ::= <sexp> * .. * <sexp>		*)
(*----------------------------------------------*)
let isSpat : SHspat.t parser =
  let isSpatExp' = token isSpatExp in
  let isAst' = token (isThisString "*") in
  many 0 isSpatExp' isAst'

(*  <sh>   ::=					*)
(*       | (Ex x y z.)? (<pexp> &) * <spat>	*)
(*       | (Ex x y z.)? (<pexp> &) <pexp>	*)
let isSH : SH.t parser =
  let errmes1 = [("ex","Write \"Ex\" \n")] in
  let errmes2 = [(":","Use \".\" \n");("(","Use \".\" \n")] in
  let errmes4 = [("*","Use \"&\" \n")] in
  let isVoid = token (isThisString "") in
  let isExPrm = many 1 (token (isIdentifier [])) isComma in
  let isExHd = isThisStringErr errmes1 "Ex " in
  let isExEnd = isThisStringErr errmes2 "." in
  let isEx1 = func (fun (_,p,_)->p) (parser3s isExHd isExPrm (token isExEnd) dummy) in
  let isEx0 = func (fun _ -> []) isVoid in
  let isEx = parserOrLst [isEx1;isEx0] in
  let isSep = isThisStringErr errmes4 "&" in
  let isPex1 = func (fun (p,_)->p) (parser2s isPureExp (token isSep) dummy) in
  let isPurePart = many0 (token isPex1) in
  let isSH_ps = parser3s isEx isPurePart isSpat dummy in
  let isSH_p = func (fun (v,ps,p) -> (v,ps@[p],[]))
    (parser3s isEx isPurePart (token isPureExp) dummy) in
  let isSH_ps1 = func (fun (v,p,s) -> (v,[p],s)) isSH_ps in
  let isSH_p1 = func (fun (v,p,s) -> (v,[p],s)) isSH_p in
  parserOrLst [isSH_p1;isSH_ps1]  

(*  <entl> ::= <sh> |- <sh> | .. | <sh>		*)
let isEntl : Entl.t parser =
  let isSH' = token isSH in
  let isBar' = token (isThisString "|") in
  let isEntlR = many 0 isSH' isBar' in
  parser2s isSH isEntlR (token (isThisString "|-"))

let isProgSet : PS.t parser =
  many1 (token isEntl)

end


