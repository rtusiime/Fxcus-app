ocamlc -o translate str.cma ecl.ml
./translate < test1.ecl > test1.c
gcc -o test1.o test1.c