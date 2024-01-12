
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t -> (f a) :: (map f t)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l0 -> if f x then x :: (filter f l0) else filter f l0

(** val eqb : char list -> char list -> bool **)

let rec eqb s1 s2 =
  match s1 with
  | [] -> (match s2 with
           | [] -> true
           | _::_ -> false)
  | c1::s1' ->
    (match s2 with
     | [] -> false
     | c2::s2' -> if (=) c1 c2 then eqb s1' s2' else false)

type ident = char list

type aexpr =
| Var of ident
| Cst of int
| Add of aexpr * aexpr
| Sub of aexpr * aexpr

type bexpr =
| Bcst of bool
| Ble of aexpr * aexpr
| Beq of aexpr * aexpr
| Bnot of bexpr
| Band of bexpr * bexpr

type prog =
| Skip
| Ite of bexpr * prog * prog
| Seq of prog * prog
| Asg of char list * aexpr
| Err
| Loop of bexpr * prog

module Oracle =
 struct
  (** val next_is_error : prog -> bool **)

  let rec next_is_error = function
  | Seq (p0, _) -> next_is_error p0
  | Err -> true
  | _ -> false
 end

module Symb =
 struct
  type store = ident -> aexpr

  type state = (bexpr * store) * prog

  (** val path : state -> bexpr **)

  let path = function
  | (p, _) -> let (path0, _) = p in path0

  (** val update : store -> ident -> aexpr -> store **)

  let update s x e y =
    if eqb y x then e else s y

  (** val aeval : store -> aexpr -> aexpr **)

  let rec aeval s e = match e with
  | Var x -> s x
  | Cst _ -> e
  | Add (e1, e2) -> Add ((aeval s e1), (aeval s e2))
  | Sub (e1, e2) -> Sub ((aeval s e1), (aeval s e2))

  (** val beval : store -> bexpr -> bexpr **)

  let rec beval s e = match e with
  | Bcst _ -> e
  | Ble (e1, e2) -> Ble ((aeval s e1), (aeval s e2))
  | Beq (e1, e2) -> Beq ((aeval s e1), (aeval s e2))
  | Bnot e0 -> Bnot (beval s e0)
  | Band (e1, e2) -> Band ((beval s e1), (beval s e2))

  (** val is_error : state -> bool **)

  let is_error = function
  | (_, prog0) -> Oracle.next_is_error prog0
 end

type 'a stream = 'a __stream Lazy.t
and 'a __stream =
| Snil
| Scons of 'a * 'a stream

(** val map0 : ('a1 -> 'a2) -> 'a1 stream -> 'a2 stream **)

let rec map0 f s =
  match Lazy.force
  s with
  | Snil -> lazy Snil
  | Scons (x, xs) -> lazy (Scons ((f x), (map0 f xs)))

type skip_case =
| Is_skip
| Is_not_skip

(** val skip_dec : prog -> skip_case **)

let skip_dec = function
| Skip -> Is_skip
| _ -> Is_not_skip

module NaiveInterpreter =
 struct
  (** val expand : bexpr -> Symb.store -> prog -> Symb.state list **)

  let rec expand path0 env = function
  | Ite (b, p1, p2) ->
    (((Band (path0, (Symb.beval env b))), env), p1) :: ((((Band (path0, (Bnot
      (Symb.beval env b)))), env), p2) :: [])
  | Seq (p1, p2) ->
    (match skip_dec p1 with
     | Is_skip -> ((path0, env), p2) :: []
     | Is_not_skip ->
       map (fun pat -> let (y, p) = pat in (y, (Seq (p, p2))))
         (expand path0 env p1))
  | Asg (x, e) ->
    ((path0, (Symb.update env x (Symb.aeval env e))), Skip) :: []
  | Loop (b, p) ->
    (((Band (path0, (Symb.beval env b))), env), (Seq (p, (Loop (b,
      p))))) :: ((((Band (path0, (Bnot (Symb.beval env b)))), env),
      Skip) :: [])
  | _ -> []

  (** val reachable : Symb.state list -> Symb.state stream **)

  let rec reachable = function
  | [] -> lazy Snil
  | s :: l0 ->
    let (p0, p) = s in
    let (path0, senv) = p0 in
    lazy (Scons (s, (reachable (app l0 (expand path0 senv p)))))
 end

type solver_result =
| SAT
| UNSAT
| TIMEOUT

module type SOLVER =
 sig
  val check_sat : bexpr -> solver_result
 end

module MakeInterpreter =
 functor (Solver:SOLVER) ->
 struct
  (** val expand : Symb.state -> ((bexpr * Symb.store) * prog) list **)

  let expand = function
  | (p, prog0) ->
    let (path0, env) = p in
    filter (fun pat0 ->
      let (y, _) = pat0 in
      let (path1, _) = y in
      (match Solver.check_sat path1 with
       | UNSAT -> false
       | _ -> true)) (NaiveInterpreter.expand path0 env prog0)

  (** val reachable : Symb.state list -> Symb.state stream **)

  let rec reachable = function
  | [] -> lazy Snil
  | s :: l0 -> lazy (Scons (s, (reachable (app l0 (expand s)))))
 end

type bug =
| SureBug of bexpr
| UnsureBug of bexpr
| NoBug

module MakeNaiveBugFinder =
 functor (Solver:SOLVER) ->
 struct
  (** val is_error : Symb.state -> bug **)

  let is_error s =
    if Symb.is_error s
    then (match Solver.check_sat (Symb.path s) with
          | SAT -> SureBug (Symb.path s)
          | UNSAT -> NoBug
          | TIMEOUT -> UnsureBug (Symb.path s))
    else NoBug

  (** val find_bugs : prog -> bexpr -> bug stream **)

  let find_bugs p ass =
    map0 is_error
      (NaiveInterpreter.reachable (((ass, (fun x -> Var x)), p) :: []))
 end

module MakeBugFinder =
 functor (Solver:SOLVER) ->
 struct
  module Interpreter = MakeInterpreter(Solver)

  (** val is_error : Symb.state -> bug **)

  let is_error s =
    if Symb.is_error s
    then (match Solver.check_sat (Symb.path s) with
          | SAT -> SureBug (Symb.path s)
          | UNSAT -> NoBug
          | TIMEOUT -> UnsureBug (Symb.path s))
    else NoBug

  (** val find_bugs : prog -> bexpr -> bug stream **)

  let find_bugs p ass =
    map0 is_error (Interpreter.reachable (((ass, (fun x -> Var x)), p) :: []))
 end
