type ide = string;;

type exp = (*tipi di dato*)
	| Eint of int 
	| Estring of string
	| Ebool of bool 
	| Den of ide 
	| Prod of exp * exp 
	| Sum of exp * exp 
	| Diff of exp * exp 
	| Eq of exp * exp 
	| Minus of exp 
	| IsZero of exp 
	| Or of exp * exp 
	| And of exp * exp 
	| Not of exp 
	| Ifthenelse of exp * exp * exp 
	| Let of ide * exp * exp 
	| Fun of ide * exp 
	| FunBin of ide * ide * exp (*funzione binaria*)
	| FunCall of exp * exp 
	| Letrec of ide * ide * exp * exp 
	| Dict of (ide * exp) list (*definizione dizionario come una lista di coppie identificatore-valore*)   
	| InsertDict of ide * exp * exp (*label, valore, dict*)    
	| DeleteDict of ide * exp (*label, dict*)      
	| HasKeyDict of ide * exp (*label, dict*)
	| IterateDict of exp * exp (*fun, dict*)
	| FoldDict of exp * exp * exp (*fun, dict, default*)
	| FilterDict of ide list * exp (*lista, dict*)


(*ambiente polimorfo*)
type 't env = (string * 't) list;; 

let emptyenv (x : 't) = [("",x)];;  

let rec applyenv ((r : 't env), (i : ide)) = match r with         
	| [(_,e)] -> e
	| (i1,e1)::xs -> if i=i1 then e1 else applyenv (xs,i)
	| [] -> failwith ("Wrong env");;

let bind (r : 't env) (i : ide) (v : 't) = (i,v)::r;;


(*tipi esprimibili*)         
type evT = 
	| Int of int 
	| String of string
	| Bool of bool 
	| Unbound 
	| FunVal of evFun     
	| FunBinVal of evFunBin
	| RecFunVal of ide * evFun 
	| DictVal of (ide * evT) list  

	and evFun = ide * exp * evT env 
	and evFunBin = ide* ide * exp * evT env;;


(*typechecker dinamico*)
let rec typecheck (s : string) (v : evT) = match s with
	| "int" -> (match v with
			| Int(_) -> true 
			| _ -> false)
	| "bool" -> (match v with
			| Bool(_) -> true 
			| _ -> false) 
	| "string" -> (match v with
			| String(_) -> true 
			| _ -> false)
	| "dictval" -> (match v with
                     	|DictVal(d) -> (match d with
                                      | [] -> true
                                      | (id,x)::xs -> if (typecheck "int" x) then checkList "int" xs
																										else if  (typecheck "bool" x) then checkList "bool" xs
																										else checkList "string" xs)
                      | _ -> false)
	| _ -> failwith("not a valid type")

  and checkList (tp: string) (l:(ide * evT) list) : bool =
      (match l with
      	| [] -> true
      	| (id,x)::xs -> (typecheck tp x) && (checkList tp xs));;

(*funzioni primitive*)
let prod x y = match ((typecheck "int" x), (typecheck "int" y), x, y) with
			|(true, true, Int(n), Int(u)) -> Int(n*u)
			|(_,_,_,_) -> failwith("Type error");;
	

let sum x y = match ((typecheck "int" x), (typecheck "int" y), x, y) with
			|(true, true, Int(n), Int(u)) -> Int(n+u)
			|(_,_,_,_) -> failwith("Type error");;

let diff x y = match ((typecheck "int" x), (typecheck "int" y), x, y) with
			|(true, true, Int(n), Int(u)) -> Int(n-u)
			|(_,_,_,_) -> failwith("Type error");;

let eq x y = match ((typecheck "int" x), (typecheck "int" y), x, y) with
			|(true, true, Int(n), Int(u)) -> Bool(n=u)
			|(_,_,_,_) -> failwith("Type error");;

let minus x = match ((typecheck "int" x), x) with
			|(true, Int(n)) -> Int(-n)
			|(_,_) -> failwith("Type error");;

let iszero x = match ((typecheck "int" x), x) with
			|(true, Int(n)) -> Bool(n=0)
			|(_,_) -> failwith("Type error");;

let vel x y = match ((typecheck "bool" x), (typecheck "bool" y),x,y) with
			|(true, true, Bool(b),Bool(e)) -> Bool(b||e)
			|(_,_,_,_) -> failwith("Type error");;

let et x y = match ((typecheck "bool" x), (typecheck "bool" y),x,y) with
			|(true, true, Bool(b),Bool(e)) -> Bool(b&&e)
			|(_,_,_,_) -> failwith("Type error");;

let non x = match ((typecheck "bool" x), x) with
			|(true, Bool(true)) -> Bool(false) 
			|(true, Bool(false)) -> Bool(true)
			|(_,_) -> failwith("Type error");;


(*altre funzioni*)
let rec memberList lista lab =     
	(match lista with
		| [] -> false
		| x::xs -> if (lab = x) then true else memberList xs lab);;

let rec member lista lab =     
			(match lista with
				| [] -> false
				| (x,y)::xs -> if (lab = x) then true else member xs lab);;


(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	| Eint n -> Int n
	| Estring s -> String s
	| Ebool b -> Bool b 
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv (r,i) 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("Not boolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r)  
	| FunBin(acc, i, a) -> FunBinVal(acc, i, a, r)   
	| FunCall(f, eArg) ->   
			let fClosure = (eval f r) in
			(match fClosure with
				| FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) 
				| RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in 
						let rEnv = (bind fDecEnv g fClosure) in 
							let aEnv = (bind rEnv arg aVal) in 
								eval fBody aEnv 
				| _ -> failwith("non functional value"))
	| Letrec(f, i, fBody, letBody) ->
        		let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                			eval letBody r1
	| Dict(thisdict) -> DictVal(evalDict thisdict r)
	| InsertDict(id,valx,thisdict) ->   
		(match (eval thisdict r) with
			| DictVal(mydict) -> if (dHasKey mydict id) then failwith("Label already used")
													 else DictVal(dInsert mydict id valx r)
			| _ -> failwith("Wrong value"))
  | DeleteDict(id,thisdict) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> if (dHasKey mydict id) then DictVal(dDelete mydict id)
														else failwith("Absent label")
			| _ -> failwith("Wrong value"))   
	| HasKeyDict(lab,thisdict) ->
		(match (eval thisdict r) with
			|DictVal(mydict) -> Bool(dHasKey mydict lab)    
			| _-> failwith("Wrong value"))   
	| IterateDict(f,thisdict) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> if (typecheck "dictval" (DictVal(mydict))) then DictVal(appIterate mydict f r)
						else failwith("Iterate wrong type")
			| _ -> failwith("Wrong value"))
	|FoldDict(f,thisdict,acc) -> 
		(match (eval thisdict r) with
			| DictVal(mydict) -> if (typecheck "dictval" (DictVal(mydict))) then appFold mydict f acc r
						else failwith("Fold wrong type")
			| _ -> failwith("Wrong value")) 
	|FilterDict(listx,thisdict) ->
		(match (eval thisdict r) with
			| DictVal(mydict) -> DictVal(appFilter mydict listx)
			| _ -> failwith("Wrong value"))

	and evalDict (dict : (ide * exp) list) (r : evT env) : (ide * evT) list = 
				let secDict = (match dict with 
					| [] -> []
					| (x,y)::xs -> if (member xs x) then failwith ("Duplicate keys") else (x, eval y r) :: evalDict xs r )
				in if (typecheck "dictval" (DictVal(secDict))) then secDict else failwith("Dict wrong type")

	and dInsert (dict : (ide * evT) list) (id : ide) (valx : exp) (r : evT env) : (ide * evT) list =
				let secDict = (id, (eval valx r))::dict  
				in if (typecheck "dictval" (DictVal(secDict))) then secDict else failwith("Insert wrong type")

	and dDelete (dict : (ide * evT) list) (id : ide) : (ide * evT) list =  
				(match dict with
					| [] -> []
					| (x,y)::xs -> if (id = x) then dDelete xs id else (x,y)::dDelete xs id)
	
	and dHasKey (dict : (ide * evT) list) (lab : ide) : bool =     
				(match dict with
					| [] -> false
					| (x,y)::xs -> if (lab = x) then true else dHasKey xs lab)
	
	and appIterate (dict : (ide * evT) list) (funz : exp) (r : evT env) : (ide * evT) list =
				(match dict with
					| [] -> []
					| (x,y)::xs -> (x, dFunCall funz y r)::appIterate xs funz r)

	and dFunCall (funz : exp) (y : evT) (r : evT env) : evT =
				let fClosure = (eval funz r) in
					(match fClosure with
						| FunVal(arg, fBody, fDecEnv) -> eval fBody (bind fDecEnv arg y) 
						| RecFunVal(g, (arg, fBody, fDecEnv)) -> 
								let rEnv = (bind fDecEnv g fClosure) in 
									let aEnv = (bind rEnv arg y) in 
										eval fBody aEnv 
						| _ -> failwith("non functional value"))

	and appFold (dict : (ide * evT) list) (f : exp) (acc : exp) (r : evT env) : evT = 
				(match f with
					| FunBin(i1,i2,a)-> (match dict with
							| [] -> eval acc r
							| (x,y)::xs -> dFunBin a r i1 i2 y (appFold xs f acc r))
					| Fun(_,_) -> failwith ("Not a binary function")
					| _ -> failwith("Not a dict"))

	and dFunBin (a : exp) (r : evT env) (i1 : ide) (i2 : ide) (y : evT) (n : evT) : evT =
					eval a (bind(bind r i2 n) i1 y)

	and appFilter (dict : (ide * evT) list) (listx : ide list) : (ide * evT) list=
				match dict with
				| [] -> [] 
				| (x,y)::xs -> if (memberList listx x) then (x,y)::appFilter xs listx else appFilter xs listx;;

(* ============================= * test interprete * ============================= *)

(* definisco ambiente vuoto*)
let env = emptyenv Unbound;;

(*creazione dizionario*)
let my_dict = Dict([("mele", Eint 44) ; ("pere", Eint 67) ; ("banane", Eint 56) ; ("fragole", Eint 98)]);;

eval my_dict env;;

(*eccezione duplicati*)
let dupl_dict = Dict([("mele", Eint 44) ; ("pere", Eint 67) ; ("banane", Eint 56) ; ("fragole", Eint 98) ; ("banane", Eint 32)]);;

eval dupl_dict env;;

(*eccezione tipi*)
let type_dict = Dict([("mele", Eint 44) ; ("pere", Ebool true) ; ("banane", Eint 56)]);;

eval type_dict env;;

(*inserimento coppia*)
let add_dict = InsertDict("kiwi", Eint 76, my_dict);;

eval add_dict env;;

(*eccezione etichetta già presente*)
let addupl_dict = InsertDict("pere", Eint 76, my_dict);;

eval addupl_dict env;;

(*eccezione tipi*)
let addtype_dict = InsertDict("kiwi", Ebool false, my_dict);;

eval addtype_dict env;;

(*rimozione coppia*)
let rm_dict = DeleteDict("mele", my_dict);;

eval rm_dict env;;

(*rimozione coppia inesistente*)
let rm2_dict = DeleteDict("pesche", add_dict);;

eval rm2_dict env;;

(*controllo presenza coppia*)
let hk_dict = HasKeyDict("mele", my_dict);;

eval hk_dict env;; (*true*)

(*funzione iterate*)
let it_dict = IterateDict(Fun("x", Sum(Den "x", Eint 1)), my_dict);;

eval it_dict env;;

(*funzione fold*)
let fold_dict = FoldDict(FunBin("acc", "x", Prod(Den "x", Den "acc")), my_dict, Eint 1);;

eval fold_dict env;;

(*funzione filter*)
let filt_dict = FilterDict (["pere" ; "fragole"], my_dict);;

eval filt_dict env;;