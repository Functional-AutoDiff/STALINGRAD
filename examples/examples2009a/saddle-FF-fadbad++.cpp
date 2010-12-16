#include <iomanip>
#include "common-fadbad++.cpp"

#define INNER 2
#define OUTER 2
#define TOTAL (INNER+OUTER)

template <typename D>
D f(D (&x)[TOTAL]) {return (x[0]*x[0]+x[1]*x[1])-(x[2]*x[2]+x[3]*x[3]);}

F<double> x1c[OUTER];

template <typename D>
D inner(D (&x2)[INNER]) {
  D x[TOTAL];
  x[0] = x1c[0];
  x[1] = x1c[1];
  x[2] = x2[0];
  x[3] = x2[1];
  return -f(x);}

template <typename D>
D outer(D (&x1)[OUTER]) {
  D x2[INNER], x2_star[INNER];
  x1c[0] = x1[0];
  x1c[1] = x1[1];
  x2[0] = 1.0;
  x2[1] = 1.0;
  return -multivariate_argmin(inner, x2, x2_star);}

int main() {
  double x1_start[OUTER], x2_start[INNER], x1_star[OUTER], x2_star[INNER];
  x1_start[0] = 1.0;
  x1_start[1] = 1.0;
  x2_start[0] = 1.0;
  x2_start[1] = 1.0;
  multivariate_argmin(outer, x1_start, x1_star);
  x1c[0] = x1_star[0];
  x1c[1] = x1_star[1];
  multivariate_argmin(inner, x2_start, x2_star);
  cout<<setprecision(18)<<x1_star[0]<<" "<<x1_star[1]<<" "<<x2_star[0]<<" "
      <<x2_star[1]<<endl;
  return 0;}
