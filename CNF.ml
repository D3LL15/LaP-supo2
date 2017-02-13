
type choice = None | Some of 'a;;

type logic = 
	| NOT of logic
	| LETTER of string;;

let rec member = function
	| (x, []) -> false
	| (x, y::ys) -> if (x = y) then true else member(x, ys);;


(* 1 *)
let rec negIsMember = function
	| (LETTER(x), ys) -> member(NOT(LETTER(x)), ys)
	| (NOT(x), ys) -> member(x, ys);;

let rec deleteTaut = function 
	| ([], _) -> []
	| (x::xs, ys) -> if (negIsMember(x,ys)) then deleteTaut(xs, ys) else x::deleteTaut(xs, x::ys);;




let rec deleteTauts = function
	| [] -> []
	| (x::xs) -> deleteTaut(x, []) :: deleteTauts(xs);;



(* 2 *)
let rec length = function 
	| [] -> 0
	| x::xs -> 1 + length(xs);;

let rec getUnitClause = function
	| [] -> (None, [])
	| (x::xs) -> if (length(x) = 1) then (Some(x), x::xs) else let (a, b) = getUnitClause(xs) in 
															(a, x::b)

let rec deleteClausesContainingx = function
	| (_, []) -> []
	| (x, y::ys) -> if (member(x, y)) then deleteClausesContainingx(ys) else y::deleteClausesContainingx(ys);;

let rec deleteXFromClause = function
	| (_, []) -> []
	| (x, y::ys) -> if (x=y) then ys else y::deleteXFromClause(x,ys);;

let rec deleteXFromAllClauses = function
	| (_, []) -> []
	| (x, y::ys) -> deleteXFromClause(x, y)::deleteXFromAllClauses(ys);;





let rec doUnitPropagation = function
	| (xs) -> let (a,b) = getUnitClause(xs) in match a with 
												| None -> xs
												| Some([c]) -> let ys = deleteClausesContainingx(c, b) 
																in match c with 
																	| NOT(n) -> doUnitPropagation(deleteXFromAllClauses(n, ys))
																	| LETTER(n) -> doUnitPropagation(deleteXFromAllClauses(NOT(n), ys));;

(* 3 *)

let rec deleteClausesContainingElementsOfX = function
	| (_, []) -> []
	| ([], ys) -> ys
	| (NOT(x)::xs, ys) -> deleteClausesContainingElementsOfX(xs, deleteClausesContainingx(x, ys))
	| (LETTER(x)::xs, ys) -> deleteClausesContainingElementsOfX(xs, deleteClausesContainingx(NOT(x), ys));;

(* clauses to go vs current clauses containing pure literals *)
let rec getPureLiteralClauses = function
	| (_, []) -> []
	| ([], ys) -> ys
	| (w::ws, ys) -> let zs = deleteClausesContainingElementsOfX(w, ys) in getPureLiteralClauses(ws, zs);;

let rec addToSet = function
	| (x, []) -> x
	| (x, y::ys) -> if (x=y) then (y::ys) else (y::addToSet(x, ys));;

let rec addElementsOfClausesToSet = function
	| ([], ys) -> ys
	| (x::xs, ys) -> addElementsofClausesToSet(xs, addXToSet(x, ys));;

let rec getPureLiterals = function
	| (xs) -> let ys = getPureLiteralClauses(xs, xs) in addElementsOfClausesToSet(ys, []);;




let rec deleteClausesWithPureLiterals = function
	| (xs) -> deleteClausesContainingElementsOfX(getPureLiterals(xs), xs);;


(* 4 *)

let rec getUnitLiterals = function
	| [] -> []
	| ([x]::xs) -> x::getUnitLiterals(xs)
	| (x::xs) -> getUnitLiterals(xs);;

let rec isRefutation = function
	| (_, []) -> false
	| (NOT(x), y::ys) -> if (x=y) then true else isRefutation(NOT(x), ys)
	| (x, NOT(y)::ys) -> if (x=y) then true else isRefutation(x, ys)
	| (x, y::ys) -> isRefutation(x, ys);;

let rec checkLiterals = function
	| [] -> false
	| (x::xs) -> if (isRefutation(x, xs)) then true else checkLiterals(xs);;




let rec checkForEmptyClause = function
	| (xs) -> checkLiterals(getUnitLiterals(xs));;

(* 5 *)

let rec checkWithLTrue = function
	| (LETTER(x), ys) -> let zs = deleteClausesContainingx(LETTER(x), ys)
					in DPLL(deleteXFromAllClauses(NOT(LETTER(x)), ys))
	| (NOT(x), ys) -> let zs = deleteClausesContainingx(NOT(x), ys)
					in DPLL(deleteXFromAllClauses(x), ys));;

let rec caseSplit = function
	| ([NOT(x)::xs]::ys) -> checkWithLTrue(x, [x::xs]::ys) AND checkWithLTrue(NOT(x), [x::xs]::ys)
	| ([LETTER(x)::xs]::ys) -> checkWithLTrue(x, [LETTER(x)::xs]::ys) AND checkWithLTrue(NOT(LETTER(x)), [x::xs]::ys);;



(* main *)

let rec DPLL = function 
	| (xs) -> let ys = deleteTauts(xs) in
				let zs = doUnitPropagation(ys) in
				let ws = deleteClausesWithPureLiterals(zs) in
				if (checkForEmptyClause(ws)) then false else if (length(xs) = 0) then true else caseSplit(xs);;




let () = print_string (DPLL(   [[LETTER(P)] , [NOT(LETTER(P))]]   ))
let () = print_string "\n"
	
	
	