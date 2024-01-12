open Parser
open Core
open Solver

module BugFinder = MakeBugFinder(Solver)
module NaiveBugFinder = MakeNaiveBugFinder(Solver)

let rec bounded_search (n : int) s bug =
  if n <= 0 then None else
  match Lazy.force s with
  | Snil -> Some bug
  | Scons (SureBug _, _) -> Some true
  | Scons (UnsureBug _, _) ->
    failwith "z3 timed out..."
  | Scons (NoBug, s) ->
    bounded_search (n - 1) s bug

let report_bugs_naive n (assumptions, prog) =
  bounded_search n (NaiveBugFinder.find_bugs prog assumptions) false

let report_bugs n (assumptions, prog) =
  bounded_search n (BugFinder.find_bugs prog assumptions) false

let time f =
  let t0 = Sys.time () in
  let res = f () in
  res, Sys.time () -. t0

let measure f =
  Solver.start_session ();
  let (r, t) = time f in
  Printf.eprintf "Query solved: %d\n" !querycount;
  Printf.eprintf "Runtime: %f sec\n" t;
  match r with
  | None -> Printf.eprintf "Timeout\n"
  | Some true -> Printf.eprintf "Bugs found\n"
  | Some false -> Printf.eprintf "No bugs\n"

let () =
  let n = 5000 in
  let p = parse_file Sys.argv.(1) in
  Printf.eprintf "\nRunning bug finder with pruning:\n";
  Printf.eprintf "-------------------\n";
  measure (fun () -> report_bugs n p);
  Printf.eprintf "Running naive bug finder:\n";
  Printf.eprintf "-------------------\n";
  flush_all ();
  measure (fun () -> report_bugs_naive n p)