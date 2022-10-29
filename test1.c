#include <stdio.h>
#include <stdlib.h>

int64_t getint() {
int64_t rtn;
switch (scanf("%lld", &rtn)) {
case EOF:
fprintf(stderr, "unexpected end of file\n");
exit(1);
case 0:
fprintf(stderr, "unexpected non-numeric input\n");
exit(1);
case 1: break;
}
return rtn;
}

void putint(int64_t x) {
printf("%lld\n", x);
}

double divide_int(int64_t n, int64_t d) {
if (d == 0) {
fprintf(stderr, "divide by zero\n");
exit(1);
}
return n/d;
}

int getreal() {
double rtn;
switch (scanf("%lf", &rtn)) {
case EOF:
fprintf(stderr, "unexpected end of file\n");
exit(1);
case 0:
fprintf(stderr, "unexpected non-numeric input\n");
exit(1);
case 1: break;
}
return rtn;
}

void putreal(double x) {
printf("%lg\n", x);
}

double divide_real(double n, double d) {
if (d == 0) {
fprintf(stderr, "divide by zero\n");
exit(1);
}
return n/d;
}

double to_real(int64_t n) {return (double) n;}
int64_t to_int(double x) {return (int64_t) x;}

int main() {
 int64_t i[4]; double *r = (double *) i;
 int64_t ti[7]; double *tr = (double *) ti;

 r[1] = getReal();
 putreal(r[1]);
 i[2] = getInt();
 putint(i[2]);
 tr[1] = r[1]<>1.0;
 if(!tr[1]) goto L1;
 tr[2] = r[1]+1.0;
 r[1] = tr[2];
 tr[3] = r[1]*2.001;
 tr[4] = r[1]*tr[3];
 tr[5] = r[1]*tr[4];
 r[1] = tr[5];
 L1:;
 r[1] = 12343.34343343;
 tr[6] = to_int(r[1]);
 i[3] = tr[6];
}
