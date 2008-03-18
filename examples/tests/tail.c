#include <stdio.h>

static double read_real(void);
static double loop(double x0,double x1,double x2,double x3,double x4,
		   double x5,double x6,double x7,double x8,double x9);
int main(void);

static double read_real(void) {
  double result;
  scanf("%lf",&result);
  return result;}

static double loop(double x0,double x1,double x2,double x3,double x4,
		   double x5,double x6,double x7,double x8,double x9) {
  if (x0!=0.0) return x0;
  return loop(x1,x2,x3,x4,x5,x6,x7,x8,x9,x0);}

int main(void) {
  double x0,x1,x2,x3,x4,x5,x6,x7,x8,x9;
  x0=read_real();
  x1=read_real();
  x2=read_real();
  x3=read_real();
  x4=read_real();
  x5=read_real();
  x6=read_real();
  x7=read_real();
  x8=read_real();
  x9=read_real();
  printf("%f\n",loop(x0,x1,x2,x3,x4,x5,x6,x7,x8,x9));}
