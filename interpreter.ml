(*
    Cimbir Cristian VR386661
	Colognese Marco	VR386474
	Rossini Mattia	VR386327

    "Linguaggi di Programmazione" - University of Verona 
    April 2017

    To test the project:
        ocaml
        #use "interpreter.ml";;

    To test the project without warnings:
        ocaml -w -0..1000
        #use "interpreter.ml";;
*)



module type STORE =
    sig
        type 't store
        type loc
        val emptystore : 't -> 't store                 (* create an empty store *)
        val allocate : 't store * 't -> loc * 't store  (* create a new memory location *)
        val update : 't store * loc * 't -> 't store    (* update the memory location *)
        val applystore : 't store * loc -> 't           (* return the value of a memory location *)
    end



module Funstore:STORE =
    struct
        type loc = int
        type 't store = loc -> 't
        let (newloc,initloc) = let count = ref(-1) in
            (fun () -> count := !count +1; !count),
                (fun () -> count := -1)
        let emptystore(x) = initloc(); function y -> x
        let applystore(x,y) = x y
        let allocate((r: 'a store) , (e:'a)) = let l = newloc() in
            (l, function lu -> if lu = l then e else applystore(r,lu))
        let update((r: 'a store) , (l:loc), (e:'a)) =
            function lu -> if lu = l then e else applystore(r,lu)
    end



module type ENV =
    sig
        type 't env                                         
        val emptyenv : 't -> 't env                         (* create empty environment *)
        val bind : 't env * string * 't -> 't env           (* Add an element to the environment *)
        val bindlist : 't env * (string list) * ('t list)   (* Add an element list to the environment *)                                                     
                            -> 't env
        val applyenv : 't env * string -> 't                (* return the value of the element *)
        exception WrongBindlist
    end



module Funenv:ENV =
    struct
        type 't env = string -> 't
        exception WrongBindlist
        let emptyenv(x) = function y -> x
        let applyenv(x,y) = x y
        let bind(r, l, e) =
            function lu -> if lu = l then e else applyenv(r,lu)
        let rec bindlist(r, il, el) = match (il,el) with
            | ([],[]) -> r
            | i::il1, e::el1 -> bindlist (bind(r, i, e), il1, el1)
            | _ -> raise WrongBindlist
    end



type ide = string
type exp =
    | Eint of int
    | Ebool of bool
    | Den of ide
    | Prod of exp * exp
    | Sum of exp * exp
    | Diff of exp * exp
    | Eq of exp * exp
    | Minus of exp
    | Iszero of exp
    | Or of exp * exp
    | And of exp * exp
    | Not of exp
    | Ifthenelse of exp * exp * exp
    | Val of exp
    | Let of ide * exp * exp
    | Fun of ide list * exp
    | Appl of exp * exp list
    | Rec of ide * exp
    | Proc of ide list * (decl * com list)
    | Newloc of exp 
    | Estring of string                         (* Add Estring in exp *)
	| Echar of char								(* Add Echar in exp *)
    | Len of exp                                (* Constructor of Length *)
    | Concat of exp * exp                       (* Constructor of Concatenation *)
    | Substr of exp * exp * exp                 (* Constructor of Substr *)
	| Equals of exp * exp						(* Constructor of Equals *)
	| Contain of exp * exp						(* Constructor of Contain *)
    | Trim of exp                               (* Constructor of Trim *)
    | Uppercase of exp                          (* Constructor of Uppercase *)
    | Lowercase of exp                          (* Constructor of Lowercase *)
and decl =(ide * exp) list * (ide * exp) list   
and com =
    | Assign of exp * exp
    | Cifthenelse of exp * com list * com list
    | While of exp * com list
    | Block of block
    | Call of exp * exp list        
    | Reflect of string                         (* Constructor od Reflect *)
and block= 
    decl * com list

exception Nonstorable
exception Nonexpressible
type eval = 
    | Int of int
    | Bool of bool
    | Novalue
    | Funval of efun
    | String of string                      	(* Constructor of string type *)
	| Char of char								(* Constructor of char type *)
and dval =
	| Dint of int
    | Dbool of bool
    | Dstring of string                     	(* Constructor of string type for enviroment *)
    | Dchar of char
	| Unbound
    | Dloc of Funstore.loc
    | Dfunval of efun
    | Dprocval of proc
and mval = 
    | Mint of int
    | Mbool of bool
    | Mstring of string                     	(* Constructor of string type for memory *)
    | Mchar of char
	| Undefined
and efun = (dval list) * (mval Funstore.store) -> eval
and proc = (dval list) * (mval Funstore.store) -> mval Funstore.store

let evaltomval e = match e with
    | Int n -> Mint n
    | Bool n -> Mbool n
    | String n -> Mstring n                 	(* From eval to mval *)
	| Char n -> Mchar n           
    | _ -> raise Nonstorable
let mvaltoeval m = match m with
    | Mint n -> Int n
    | Mbool n -> Bool n
    | Mstring n -> String n                 	(* From mval to eval *)
	| Mchar n -> Char n
    | _ -> Novalue
let evaltodval e = match e with
    | Int n -> Dint n
    | Bool n -> Dbool n
    | String n -> Dstring n                 	(* From eval to dval *)
	| Char n -> Dchar n
    | Novalue -> Unbound
    | Funval n -> Dfunval n
let dvaltoeval e = match e with
    | Dint n -> Int n
    | Dbool n -> Bool n
    | Dstring n -> String n                 	(* From dval to eval *)
	| Dchar n -> Char n
    | Dloc n -> raise Nonexpressible
    | Dfunval n -> Funval n
    | Dprocval n -> raise Nonexpressible
    | Unbound -> Novalue



let typecheck (x, y) = match x with
    | "int" -> (match y with
        | Int u -> true
        | _ -> false)
    | "bool" -> (match y with
        | Bool u -> true
        | _ -> false)
    | "string" -> (match y with         	(* return "true" only if it's a string *)
        | String(u) -> true
        | _ -> false)
	| "char" -> (match y with
		| Char u -> true
		| _ -> false)
    | _ -> failwith ("not a valid type")



let minus x = if typecheck("int",x) then (match x with Int(y) -> Int(-y) )
    else failwith ("type error")

let iszero x = if typecheck("int",x) then (match x with Int(y) -> Bool(y=0) )
    else failwith ("type error")

let equ (x,y) = if typecheck("int",x) && typecheck("int",y)
    then (match (x,y) with (Int(u), Int(w)) -> Bool(u = w))
    else failwith ("type error")

let plus (x,y) = if typecheck("int",x) && typecheck("int",y)
    then (match (x,y) with (Int(u), Int(w)) -> Int(u+w))
    else failwith ("type error")

let diff (x,y) = if typecheck("int",x) && typecheck("int",y)
    then (match (x,y) with (Int(u), Int(w)) -> Int(u-w))
    else failwith ("type error")

let mult (x,y) = if typecheck("int",x) && typecheck("int",y)
    then (match (x,y) with (Int(u), Int(w)) -> Int(u*w))
    else failwith ("type error")

let et (x,y) = if typecheck("bool",x) && typecheck("bool",y)
    then (match (x,y) with (Bool(u), Bool(w)) -> Bool(u && w))
    else failwith ("type error")

let vel (x,y) = if typecheck("bool",x) && typecheck("bool",y)
    then (match (x,y) with (Bool(u), Bool(w)) -> Bool(u || w))
    else failwith ("type error")

let non x = if typecheck("bool",x)
    then (match x with Bool(y) -> Bool(not y) )
    else failwith ("type error")



	(* STRING's FUNCTIONS *)
let len x =                 (* INPUT: string		OUTPUT: string's length *)
    if typecheck("string", x)
        then (match x with String(u) -> Int(String.length u))
        else failwith("type error")

let concat (x,y) =           (* INPUT: (string, string)		OUTPUT: the concatenation of the two strings *)
    if typecheck("string",x) && typecheck("string",y)
        then (match (x,y) with (String(u),String(w)) -> String(String.concat "" [u;w]) )
        else failwith("type error")

let substr (x,y,z) =         (* INPUT: (string, start, end)		OUTPUT: the substring starting from "start" to "end" *)
    if typecheck("string",x) && typecheck("int",y) && typecheck("int",z)
        
        then (match (x,y,z) with (String(s),Int(i),Int(j)) -> String(  
            if (j-i)>0
                then    String.sub s i (j-i+1)    
                else    ""
        ))
        else failwith("type error")

let trim x =                (* INPUT: string		OUTPUT: the string without spaces at the edges *)
    if typecheck("string", x)
        then (match x with String(u) -> String(String.trim u))
        else failwith("type error")

let uppercase x =           (* INPUT: string		OUTPUT: the string in uppercase *)
    if typecheck("string", x)
        then (match x with String(u) -> String(String.uppercase_ascii u))
        else failwith("type error")

let lowercase x =           (* INPUT: string		OUTPUT: the string in lowercase *)
    if typecheck("string", x)
        then (match x with String(u) -> String(String.lowercase_ascii u))
        else failwith("type error")
		
let equals (x, y) =			(* INPUT: (string, string)		OUTPUT: "true" if strings are equals, "false" otherwise *)
    if typecheck("string",x) && typecheck("string",y)
        then (match (x,y) with (String(u),String(w)) -> Bool(String.equal u w) )
    else failwith("type error")

let contain (x, y) =		(* INPUT: (string, char)		OUTPUT: "true" if the string contains the character, "false" otherwise *)
    if typecheck("string",x) && typecheck("char",y)
        then (match (x,y) with (String(u),Char(w)) -> Bool(String.contains u w) )
    else failwith("type error")

let explode s =             (* INPUT: string		OUTPUT: converts the string into a list of char *)
    let rec expl i l =
        if i < 0 then l else
            expl (i - 1) (s.[i] :: l) in
    expl (String.length s - 1) [];;

let implode l =             (* INPUT: list of char		OUTPUT: converts the list of char into a string *)
    let result = String.create (List.length l) in
    let rec imp i = function
    | [] -> result
    | c :: l -> result.[i] <- c; imp (i + 1) l in
    imp 0 l;;



let stringSplitToList c s =	(* INPUT: char string		OUTPUT: divides the string using the given character, ignoring characters inside brackets *)
    let sl = String.length s in
    let rec loop fine parentesi parentesiQ t i=
        if i<0 then (String.sub s (i+1) (fine-(i)) :: t)
        else if s.[i]==c && parentesi==0 && parentesiQ==0 then loop (i-1) (parentesi)  (parentesiQ) (String.sub s (i+1) (fine-(i)) :: t) (i-1) 
        else if s.[i]=='(' then loop (fine) (parentesi-1) (parentesiQ) t (i-1)
        else if s.[i]==')' then loop (fine) (parentesi+1) (parentesiQ) t (i-1)
        else if s.[i]=='[' then loop (fine) (parentesi) (parentesiQ-1) t (i-1)
        else if s.[i]==']' then loop (fine) (parentesi) (parentesiQ+1) t (i-1)
		else loop (fine) (parentesi) (parentesiQ) t (i-1)
    in
    loop (String.length s - 1) 0 0 [] (String.length s - 1)

	
									
let replaceChar s c1 c2 =	(* INPUT: string, charToReplace, newChar		OUTPUT: string without charToReplace, replaced by newChar *)
	let sl=String.length s in
	let rec loop i =
    	if i<0 then s
    	else if s.[i]==c1 then let a = s.[i]<-c2 in
			loop (i-1)
		else loop (i-1)
    in
    loop (sl - 1)
	


let rec stringToExp x =		(* INPUT: string		OUTPUT: expression represented by the string *)
    let s = explode x in
    match s with
    |   'E'::'i'::'n'::'t'::'('::r ->   Eint(int_of_string (String.sub (implode r) 0 (String.length (implode r) - 1)) )   
    |   'E'::'s'::'t'::'r'::'i'::'n'::'g'::'('::r ->  Estring(String.sub (implode r) 1 ((String.length (implode r)) - 3))
    |   'E'::'b'::'o'::'o'::'l'::'('::r ->  Ebool(bool_of_string (String.sub (implode r) 0 (String.length (implode r) - 1)))  
    |   'D'::'e'::'n'::'('::r ->    Den(String.sub (implode r) 1 ((String.length (implode r)) - 3))
    |   'V'::'a'::'l'::'('::r ->    Val(stringToExp (String.sub (implode r) 0 (String.length (implode r) - 1)))
    |   'N'::'o'::'t'::'('::r ->    Not(stringToExp (String.sub (implode r) 0 (String.length (implode r) - 1)))
    |   'E'::'q'::'('::r -> 
                    let l = stringSplitToList (',') (String.sub (implode r) 0 (String.length (implode r) - 1)) in
                        if (List.length l) != 2  then failwith ("Errore sintassi, " ^ (implode s) )
                        else Eq(stringToExp(List.hd l) , stringToExp(List.hd (List.tl l)))
    |   'I'::'s'::'z'::'e'::'r'::'o'::'('::r ->    Iszero(stringToExp (String.sub (implode r) 0 (String.length (implode r) - 1)))
    |   'P'::'r'::'o'::'d'::'('::r -> 
                    let l = stringSplitToList (',') (String.sub (implode r) 0 (String.length (implode r) - 1)) in
                        if (List.length l) != 2  then failwith ("Errore sintassi, " ^ (implode s) )
                        else Prod(stringToExp(List.hd l) , stringToExp(List.hd (List.tl l)))
    |   'D'::'i'::'f'::'f'::'('::r -> 
                    let l = stringSplitToList (',') (String.sub (implode r) 0 (String.length (implode r) - 1)) in
                        if (List.length l) != 2  then failwith ("Errore sintassi, " ^ (implode s) )
                        else Diff(stringToExp(List.hd l) , stringToExp(List.hd (List.tl l)))
    | _ -> failwith ("Errore sintassi, stringToExp, " ^ (implode s))



let rec stringToCom x =		(* INPUT: string		OUTPUT: command represented by the string *)    
    let s = explode x in
    match s with
    |   'A'::'s'::'s'::'i'::'g'::'n'::'('::r -> 
            let l = stringSplitToList (',') (String.sub (implode r) 0 (String.length (implode r) - 1)) in
                if (List.length l) != 2  then failwith ("Errore sintassi, " ^ (implode s) )
                else Assign(stringToExp(List.hd l) , stringToExp(List.hd (List.tl l)))

    |   'C'::'i'::'f'::'t'::'h'::'e'::'n'::'e'::'l'::'s'::'e'::'('::r ->
            let l = stringSplitToList (',') (String.sub (implode r) 0 (String.length (implode r) - 1)) in
                if (List.length l) != 3  then failwith ("Errore sintassi, " ^ (implode s))
                else Cifthenelse(stringToExp(List.hd l) , 
                                reflect(String.sub (List.hd (List.tl l)) 1 (String.length (List.hd (List.tl l)) - 2)),
                                reflect(String.sub (List.hd (List.tl (List.tl l))) 1 (String.length (List.hd (List.tl (List.tl l))) - 2))
                                )

    |   'W'::'h'::'i'::'l'::'e'::'('::r -> 
            let l = stringSplitToList (',') (String.sub (implode r) 0 (String.length (implode r) - 1)) in
                if (List.length l) != 2  then failwith ("Errore sintassi, " ^ (implode s))
                else While(stringToExp(List.hd l) , 
                                reflect(String.sub (List.hd (List.tl l)) 1 (String.length (List.hd (List.tl l)) - 2))
                                )
    
    | _ -> failwith ("Errore sintassi, stringToCom, " ^ (implode s))


and reflect (s:string) = List.map stringToCom (stringSplitToList ';' s)	 (* INPUT: string		OUTPUT: commands list represented by the string *)
    


let rec makefun ((a:exp),(x:dval Funenv.env)) = match a with
    | Fun(ii,aa) -> Dfunval(function (d, s) -> sem aa (Funenv.bindlist (x, ii, d)) s)
    | _ -> failwith ("Non-functional object, makefun")

and makefunrec (i, Fun(ii, aa), r) =
    let functional ff (d, s1) =
    let r1 = Funenv.bind(Funenv.bindlist(r, ii, d), i, Dfunval(ff)) in sem aa r1 s1 in
    let rec fix = function x -> functional fix x in Funval(fix)

and makeproc ((a:exp),(x:dval Funenv.env)) = match a with
    | Proc(ii,b) -> Dprocval(function (d, s) -> semb b (Funenv.bindlist (x, ii, d)) s)
    | _ -> failwith ("Non-functional object, makeproc")

and applyfun ((ev1:dval),(ev2:dval list), s) = match ev1 with
    | Dfunval(x) -> x (ev2, s)
    | _ -> failwith ("attempt to apply a non-functional object, applyfun")

and applyproc ((ev1:dval),(ev2:dval list), s) = match ev1 with
    | Dprocval(x) -> x (ev2, s)
    | _ -> failwith ("attempt to apply a non-functional object, applyproc")



and sem (e:exp) (r:dval Funenv.env) (s: mval Funstore.store) =
    match e with
    | Eint(n) -> Int(n)
    | Ebool(b) -> Bool(b)
    | Estring(a) -> String(a)
	| Echar(a) -> Char(a)
    | Den(i) -> dvaltoeval(Funenv.applyenv(r,i))
    | Iszero(a) -> iszero((sem a r s) )
    | Eq(a,b) -> equ((sem a r s) ,(sem b r s) )
    | Prod(a,b) -> mult ( (sem a r s), (sem b r s))
    | Sum(a,b) -> plus ( (sem a r s), (sem b r s))

    | Len(a) -> len( (sem a r s) )                                      (* return string's length *)
    | Concat(a,b) -> concat((sem a r s), (sem b r s))                   (* return the concatenation of the two strings *)
    | Substr(a,b,c) -> substr((sem a r s),(sem b r s),(sem c r s))      (* return the cutted string *)
	| Equals(a,b) -> equals((sem a r s),(sem b r s))					(* return "true" if the strings are equal, "false" otherwise *)
   	| Contain(a,b) -> contain((sem a r s), (sem b r s))					(* return "true" if the string contains the character, "false" otherwise *)
    | Trim(a) -> trim(((sem a r s)))                                    (* return the string without spaces at the edges *)
    | Lowercase(a) -> lowercase (((sem a r s)))                         (* return the string in lowercase *)
    | Uppercase(a) -> uppercase (((sem a r s)))                         (* return the string in uppercase *)

    | Diff(a,b) -> diff ( (sem a r s), (sem b r s))
    | Minus(a) -> minus( (sem a r s))
    | And(a,b) -> et ( (sem a r s), (sem b r s))
    | Or(a,b) -> vel ( (sem a r s), (sem b r s))
    | Not(a) -> non( (sem a r s))
    | Ifthenelse(a,b,c) ->
        let g = sem a r s in
        if typecheck("bool",g) then
            (if g = Bool(true)
            then sem b r s
            else sem c r s)
        else failwith ("nonboolean guard")
    | Val(e) -> let (v, s1) = semden e r s in (match v with
        | Dloc n -> mvaltoeval(Funstore.applystore(s1, n))
        | _ -> failwith("not a variable"))
    | Let(i,e1,e2) -> let (v, s1) = semden e1 r s in sem e2 (Funenv.bind (r ,i, v)) s1
    | Fun(i,e1) -> dvaltoeval(makefun(e,r))
    | Rec(i,e1) -> makefunrec(i, e1, r)
    | Appl(a,b) -> let (v1, s1) = semlist b r s in applyfun(evaltodval(sem a r s), v1, s1) 
    | _ -> failwith ("nonlegal expression for sem")


and semden (e:exp) (r:dval Funenv.env) (s: mval Funstore.store) = match e with
    | Den(i) -> (Funenv.applyenv(r,i), s)
    | Fun(i, e1) -> (makefun(e, r), s)
    | Proc(il, b) -> (makeproc(e, r), s)
    | Newloc(e) -> let m = evaltomval(sem e r s) in let (l, s1) = Funstore.allocate(s, m) in (Dloc l, s1)
    | _ -> (evaltodval(sem e r s), s)


and semlist el r s = match el with
    | [] -> ([], s)
    | e::el1 -> let (v1, s1) = semden e r s in let (v2, s2) = semlist el1 r s1 in (v1 :: v2, s2)


and semc (c: com) (r:dval Funenv.env) (s: mval Funstore.store) = match c with
    | Assign(e1, e2) -> let (v1, s1) = semden e1 r s in (match v1 with
        | Dloc(n) -> Funstore.update(s, n, evaltomval(sem e2 r s))
        | _ -> failwith ("wrong location in assignment"))

    | Cifthenelse(e, cl1, cl2) -> let g = sem e r s in
        if typecheck("bool",g) then
            (if g = Bool(true) then semcl cl1 r s else semcl cl2 r s)
        else failwith ("nonboolean guard")

    | While(e, cl) ->
        let functional ((fi: mval Funstore.store -> mval Funstore.store)) =
            function sigma ->
                let g = sem e r sigma in
                    if typecheck("bool",g) then
                        (if g = Bool(true) then fi(semcl cl r sigma) else sigma)
                    else failwith ("nonboolean guard")
        in
        let rec ssfix = function x -> functional ssfix x in ssfix(s)

    | Call(e1, e2) -> let (p, s1) = semden e1 r s in let (v, s2) = semlist e2 r s1 in
        applyproc(p, v, s2)

    | Block(b) -> semb b r s

    | Reflect(a) -> semcl (reflect(a)) r s		(* return the commands list rappresented by the string *)


and semcl cl r s = match cl with
    | [] -> s
    | c::cl1 -> semcl cl1 r (semc c r s)

and semb ((dl, rdl), cl) r s =
    let (r1, s1) = semdl (dl, rdl) r s in semcl cl r1 s1

and semdl (dl, rl) r s = let (r1, s1) = semdv dl r s in
        semdr rl r1 s1
		
and semdv dl r s = match dl with
    | [] -> (r,s)
    | (i,e)::dl1 -> let (v, s1) = semden e r s in
        semdv dl1 (Funenv.bind(r, i, v)) s1

and semdr rl r s =  match rl with
    | [] -> (r,s)
    | (i,e)::rl1 -> let (v, s2) = semden e r s in
            let (r2, s3) = semdr rl1 (Funenv.bind(r, i, v)) s in (r2,s)



(* ---------------------- TESTS ---------------------- *)

(* 1 - TEST len *)
let s1 = Estring("Linguaggi");;
let ex1 = Len s1;;
let rho1 = Funenv.emptyenv(Unbound);;
let sigma1 = Funstore.emptystore(Undefined);;
let result1 = sem ex1 rho1 sigma1;;

(* 2 - TEST concat *)
let s2 = Estring(" di Programmazione");;
let ex2 = Concat(s1, s2);;
let rho2 = Funenv.emptyenv(Unbound);;
let sigma2 = Funstore.emptystore(Undefined);;
let result2 = sem ex2 rho2 sigma2;;

(* 3 - TEST substr *)
let ex3 = Substr(ex2, Eint(1), Eint(5));;
let rho3 = Funenv.emptyenv(Unbound);;
let sigma3 = Funstore.emptystore(Undefined);;
let result3 = sem ex3 rho3 sigma3;;

(* 4 - TEST trim *)
let s4 = Estring("   Linguaggi di Programmazione  ");;
let ex4 = Trim(s4);;
let rho4 = Funenv.emptyenv(Unbound);;
let sigma4 = Funstore.emptystore(Undefined);;
let result4 = sem ex4 rho4 sigma4;;

(* 5 - TEST uppercase *)
let ex5 = Uppercase(s1);;
let rho5 = Funenv.emptyenv(Unbound);;
let sigma5 = Funstore.emptystore(Undefined);;
let result5 = sem ex5 rho5 sigma5;;

(* 6 - TEST lowercase *)
let ex6 = Lowercase(s1);;
let rho6 = Funenv.emptyenv(Unbound);;
let sigma6 = Funstore.emptystore(Undefined);;
let result6 = sem ex6 rho6 sigma6;;

(* 7 - TEST equals *)
let s7 = Estring("Linguaggi");;
let st7 = Estring("Linguaggi");;
let ex7 = Equals(s7,st7)
let rho7 = Funenv.emptyenv(Unbound);;
let sigma7 = Funstore.emptystore(Undefined);;
let result7 = sem ex7 rho7 sigma7;;

(* 8 - TEST contain *)
let c8 = Echar('g');;
let ex8 = Contain(s7,c8);;
let rho8 = Funenv.emptyenv(Unbound);;
let sigma8 = Funstore.emptystore(Undefined);;
let result8 = sem ex8 rho8 sigma8;;
	
(* 9 - TEST explode *)
let s9 = "Linguaggi";;
let ex9 = explode s9;;

(* 10 - TEST implode *)
let ex10 = implode ex9;;

(* 11 - TEST stringSplitToList *)
let s11 = "Linguaggi";;
let c11 = 'g';;
let result11 = stringSplitToList c11 s11;;

(* 12 - TEST replaceChar *)
let c12 = 'a';;
let result12 = replaceChar s11 c11 c12;;

(* 13 - TEST stringToExp *)
let s13 = "Estring(\"Linguaggi\")";;
let st13 = stringToExp s13;;
let rho13 = Funenv.emptyenv(Unbound);;
let sigma13 = Funstore.emptystore(Undefined);;
let result13 = sem st13 rho13 sigma13;;

(* 14 - TEST stringToCom *)
let d14 = [("x",Newloc(Eint 4));("y",Newloc(Eint 1))];;
let (rho14, sigma14) = semdv d14 (Funenv.emptyenv Unbound) (Funstore.emptystore Undefined);;
let s14 = "While(Not(Eq(Val(Den(\"x\")),Eint(0))),[Assign(Den(\"y\"),Prod(Val(Den(\"y\")),Val(Den(\"x\"))));Assign(Den(\"x\"),Diff(Val(Den(\"x\")),Eint(1)))])";;
let es14 = stringToCom s14;;
let result14 = semc es14 rho14 sigma14;;
let result14Y = sem (Val(Den "y")) rho14 result14;;


(* 15 - TEST Let, Fun, Rec *)
(*
    fact(x)
		if(x==0)
			then 1
		else
			x*fact(x-1)
	result=fact(4)
*)
let es15 = Let("fact",
    		Rec("fact",
        		Fun(
            		["x"], 
            		Ifthenelse(
                		Eq(Den "x", Eint 0), 
                		Eint 1,
               			Prod(Den "x", Appl(Den "fact", [Diff(Den "x", Eint 1)]))
            		)
        		)
    		),
    		Appl(Den "fact",[Eint 5])
 		  )
let rho15 = Funenv.emptyenv(Unbound);;
let sigma15 = Funstore.emptystore(Undefined);;
let result15 = sem es15 rho15 sigma15;;

(* 16 - TEST Block *)
(*
    z=4
    w=1
    while(z!=0){
        w=w*z
        z=z-1
    }
*)
let d16 = ([("z",Newloc(Eint 4));("w",Newloc(Eint 1))],[]);;
let es16 = 	[While(Not(Eq(Val(Den "z"), Eint 0)),
    		[Assign(Den "w", Prod(Val(Den "w"),Val(Den "z")));
    		 Assign(Den "z", Diff(Val(Den "z"), Eint 1))]);
    		 Assign(Den "y", Val(Den "w"))
    		];;
let (es16: block) = (d16,es16);;
let dl16 = [("y",Newloc(Eint 0))];;
let (rho16, sigma16) = semdv dl16 (Funenv.emptyenv Unbound) (Funstore.emptystore Undefined);;
let result16 = semb es16 rho16 sigma16;;
let result16Y = sem (Val(Den "y")) rho16 result16;;

(* 17 - TEST Block, procedure, function *)
(*
    int r=0
    mul2(int x)
        return x*2
    testproc(int n){
        w=1
        w=n+1
        r=mul(w)
    }
    testproc(4)
*)
let(es17: block) =
 (  ([],
    [
        ("mult2", Fun(["x"], 
                Prod(Eint 2, Den "x"))        
        );
        ("procedure", Proc( ["n"],
        		(([("z", Newloc(Den "n"));("w", Newloc(Eint 1))],
            	[]),
                [ 
                	Assign(Den "w",Sum(Val(Den "z"),Val(Den "w")));
                  	Assign (Den "r", Appl (Den "mult2", [Val(Den "w")]))
             	])
                )
        )
    ]),
    [ Call(Den "procedure", [Eint 4])]
);;

let dr17 = [("r",Newloc(Eint 0))];;
let (rho17, sigma17) = semdv dr17 (Funenv.emptyenv Unbound) (Funstore.emptystore Undefined);;
let result17 = semb es17 rho17 sigma17;;
let result17R = sem (Val(Den "r")) rho17 result17;;

(* 18 - TEST reflect with "if" *)
(*
    z=1
    z=2
    if(false)   
        then z=5
        else z=10
*)
let d18 = [("z",Newloc(Eint 1))];;
let es18 = Reflect("Assign(Den(\"z\"),Eint(2));Cifthenelse(Ebool(false),[Assign(Den(\"z\"),Eint(5))],[Assign(Den(\"z\"),Eint(10))])");;
let cl18 = reflect("Assign(Den(\"z\"),Eint(2));Cifthenelse(Ebool(false),[Assign(Den(\"z\"),Eint(5))],[Assign(Den(\"z\"),Eint(10))])");;
let (rho18, sigma18) = semdv d18 (Funenv.emptyenv Unbound) (Funstore.emptystore Undefined);;
let result18 = semc es18 rho18 sigma18
let result18Z = sem (Val(Den "z")) rho18 result18;;

(* 19 - TEST reflect, while, expressions *)
(*
    z=4
    w=1
    while(!(z==0)){
        w=w*z
        z=z-1
    }
*)
let d19 = [("z",Newloc(Eint 4));("w",Newloc(Eint 1))];;
let es19 = Reflect("While(Not(Eq(Val(Den(\"z\")),Eint(0))),[Assign(Den(\"w\"),Prod(Val(Den(\"w\")),Val(Den(\"z\"))));Assign(Den(\"z\"),Diff(Val(Den(\"z\")),Eint(1)))])");;
(* creo com list per debug*)
let cl19 = reflect("While(Not(Eq(Val(Den(\"z\")),Eint(0))),[Assign(Den(\"w\"),Prod(Val(Den(\"w\")),Val(Den(\"z\"))));Assign(Den(\"z\"),Diff(Val(Den(\"z\")),Eint(1)))])")
let (rho19, sigma19) = semdv d19 (Funenv.emptyenv Unbound) (Funstore.emptystore Undefined);;
let sigma19final = semc es19 rho19 sigma19;;
let result19Z = sem (Val(Den "z")) rho19 sigma19final;;
let result19W = sem (Val(Den "w")) rho19 sigma19final;;