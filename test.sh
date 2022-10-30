ocamlc -o translate str.cma ecl.ml
./translate < ./test_files/gcd_prog > ./test_files/gcd_prog_my.c
./translate < ./test_files/prime_prog > ./test_files/prime_prog_my.c
./translate < ./test_files/sqrt_prog > ./test_files/sqrt_prog_my.c
./translate < ./test_files/while_prog > ./test_files/while_prog_my.c
#gcc -o test1.o test1.c