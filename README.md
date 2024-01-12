# Formal Verification of Symbolic Bug Finders

This repository contains the source code accompanying the master thesis **Formal Verification of Symbolic Bug Finders**.

## Structure

+ The file `bug.v` contains a Coq formalization of an automated bug finder by symbolic execution with its proof of correctness
+ The file `core.ml` contains the extraction of the Coq sources to OCaml (it can be generated automatically by compiling `bug.v`)
+ The files `minibug.ml`, `solver.ml`, `parser.ml` are OCaml sources for the front-end of the bug finder.

## Compilation

The project can be compiled simply by using the `make` command.
Compiling this project requires a working installation of the OCaml compiler, the Coq proof assistant, and the Dune build system.
The project has been tested to work with the following versions of these packages:
+ OCaml 4.14.1
+ Dune 3.11.1
+ Coq 8.16.1

## Usage

To execute the bug finder on examples, the command is: `dune exec minibug.exe -- <file.bug>`.

Examples `.bug` files corresponding to the examples discussed in the thesis are provided:

+ `test_gcd.bug`
+ `test_bounded.bug`
+ `test_deep_100.bug`
+ `test_deep_500.bug`
+ `test_deep_1000.bug`