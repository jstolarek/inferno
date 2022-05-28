.DEFAULT_GOAL := build

.PHONY: clean
clean:
	rm -f *~ src/*~
	dune clean

.PHONY: build
build:
	dune build _build/default/naive/Testing.exe
