
type 'a choice = None | Some of 'a;;

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

let rec isTaut = function
	| ([]) -> false
	| (x::xs) -> if (negIsMember(x,xs)) then true else isTaut(xs);;


let rec deleteTauts = function
	| [] -> []
	| (x::xs) -> if isTaut(x) then deleteTauts(xs) else  x::deleteTauts(xs);;



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
	| (x, y::ys) -> if (member(x, y)) then deleteClausesContainingx(x, ys) else y::deleteClausesContainingx(x, ys);;

let rec deleteXFromClause = function
	| (_, []) -> []
	| (x, y::ys) -> if (x=y) then ys else y::deleteXFromClause(x,ys);;

let rec deleteXFromAllClauses = function
	| (_, []) -> []
	| (x, y::ys) -> deleteXFromClause(x, y)::deleteXFromAllClauses(x, ys);;


let rec deleteEmptyClauses = function
	| [] -> []
	| (x::xs) -> if (length(x) = 0) then deleteEmptyClauses(xs) else x::deleteEmptyClauses(xs);;


let rec doUnitPropagation = function
	| (xs) -> let zs = deleteEmptyClauses(xs) in let (a,b) = getUnitClause(zs) in match a with 
												| None -> zs
												| Some([c]) -> let ys = deleteClausesContainingx(c, b) 
																in match c with 
																	| NOT(n) -> doUnitPropagation(deleteXFromAllClauses(n, ys))
																	| LETTER(n) -> doUnitPropagation(deleteXFromAllClauses(NOT(LETTER(n)), ys));;
																

(* 3 *)

let rec deleteClausesContainingElementsOfX = function
	| (_, []) -> []
	| ([], ys) -> ys
	| (NOT(x)::xs, ys) -> deleteClausesContainingElementsOfX(xs, deleteClausesContainingx(x, ys))
	| (LETTER(x)::xs, ys) -> deleteClausesContainingElementsOfX(xs, deleteClausesContainingx(NOT(LETTER(x)), ys));;

(* clauses to go vs current clauses containing pure literals *)
let rec getPureLiteralClauses = function
	| (_, []) -> []
	| ([], ys) -> ys
	| (w::ws, ys) -> let zs = deleteClausesContainingElementsOfX(w, ys) in getPureLiteralClauses(ws, zs);;

let rec addToSet = function
	| (x, []) -> [x]
	| (x, y::ys) -> if (x=y) then (y::ys) else (y::addToSet(x, ys));;

let rec addElementsOfClauseToSet = function
	| ([], ys) -> ys
	| (x::xs, ys) -> addElementsOfClauseToSet(xs, addToSet(x, ys));;


let rec addElementsOfClausesToSet = function
	| ([], ys) -> ys
	| ([]::xs, ys) -> addElementsOfClausesToSet(xs, ys)
	| (x::xs, ys) -> addElementsOfClausesToSet(xs, addElementsOfClauseToSet(x, ys));;

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


(* main *)
let rec logicPrint = function
	| NOT(LETTER(x)) -> print_string(String.concat "" [" NOT("; x; ") "])
	| LETTER(x) -> print_string(x) ;;

let rec printClause = function
	| [] -> ()
	| x::xs -> let () = logicPrint(x) in printClause(xs);;

let rec printClauses = function
	| [] -> print_string("empty set of clauses\n")
	| x::xs -> let () = let () = print_string("clause:") in printClause(x) in printClauses(xs);;

let rec dpll = function 
	| (xs) -> let ys = deleteTauts(xs) in let () = printClauses(ys) in
				if (checkForEmptyClause(ys)) then false else 
				let zs = doUnitPropagation(ys) in let () = printClauses(zs) in
				let ws = deleteClausesWithPureLiterals(zs) in let () = printClauses(ws) in
				(*if (checkForEmptyClause(ws)) then false else *)if (length(ws) = 0) then true else let (f::fs) = ws in let (u::us) = f in
						match u with 
							| NOT(n) -> let js = deleteClausesContainingx(NOT(n), ws)
														in let ks = deleteClausesContainingx(n, js)
														in dpll(deleteXFromAllClauses(n, ks)) || dpll(deleteXFromAllClauses(NOT(n), ks))
							| LETTER(n) -> let js = deleteClausesContainingx(LETTER(n), ws)
														in let ks = deleteClausesContainingx(NOT(LETTER(n)), js)
														in dpll(deleteXFromAllClauses(NOT(LETTER(n)), ks)) || dpll(deleteXFromAllClauses(LETTER(n), ks));;




let () = if dpll(   [[LETTER("P")] ; [NOT(LETTER("P"))]]   ) then print_string ("true\n") else print_string("false\n")
let () = if dpll(   [[LETTER("P")] ; [LETTER("P")]]   ) then print_string ("true\n") else print_string("false\n")
let () = if dpll(   [[LETTER("P")] ; [NOT(LETTER("P")); LETTER("P")]]   ) then print_string ("true\n") else print_string("false\n")
let () = print_string "\n"
	
	
	