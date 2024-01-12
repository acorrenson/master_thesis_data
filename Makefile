all:
	@echo "compiling coq sources"
	coqc bug.v
	@echo "compiling OCaml front-end"
	dune build

