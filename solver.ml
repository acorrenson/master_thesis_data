open Z3
open Z3.Solver
open Z3.Arithmetic
open Core

let querycount = ref 0

module Solver = struct
  let ctx = mk_context []
  
  let rec mk_expr (e : Core.aexpr) =
    match e with
    | Var n -> Integer.mk_const ctx (Symbol.mk_string ctx (Opal.implode n))
    | Cst c -> Integer.mk_numeral_i ctx c
    | Add (e1, e2) -> mk_add ctx [mk_expr e1; mk_expr e2]
    | Sub (e1, e2) -> mk_sub ctx [mk_expr e1; mk_expr e2]

  let rec mk_form (e : Core.bexpr) =
    match e with
    | Bcst true -> Boolean.mk_true ctx
    | Bcst false -> Boolean.mk_false ctx
    | Band (l, r) -> Boolean.mk_and ctx [mk_form l; mk_form r]
    | Ble (e1, e2) -> mk_le ctx (mk_expr e1) (mk_expr e2)
    | Beq (e1, e2) -> Boolean.mk_eq ctx (mk_expr e1) (mk_expr e2)
    | Bnot f -> Boolean.mk_not ctx (mk_form f)

  

  let world : (bexpr, solver_result) Hashtbl.t = Hashtbl.create 1024

  let start_session () =
    Hashtbl.clear world;
    querycount := 0

  let really_check_sat (f : Core.bexpr) =
    incr querycount;
    let slv = mk_simple_solver ctx in
    let pro = Expr.simplify (mk_form f) None in
    add slv [pro];
    match check slv [] with
    | SATISFIABLE -> SAT
    | UNSATISFIABLE -> UNSAT
    | UNKNOWN -> TIMEOUT

  let check_sat (f : Core.bexpr) =
    match Hashtbl.find_opt world f with
    | Some res -> res
    | None ->
      let res = really_check_sat f in
      Hashtbl.add world f res;
      res
end