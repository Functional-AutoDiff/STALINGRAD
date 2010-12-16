#include <iomanip>
#include "common-fadbad++.cpp"

#define CONTROLS 1
#define DIMS 2
#define CHARGES 2

F<F<double> > charges[CHARGES][DIMS];

template <typename D>
D p(D (&x)[DIMS]) {
  D r = 0.0;
  for (int l = 0; l<CHARGES; l++) r += 1.0/distance(x, charges[l]);
  return r;}

template <typename D>
D naive_euler(D (&w)[CONTROLS]) {
  D x[DIMS], xdot[DIMS], delta_t = 1e-1, g[DIMS], xddot[DIMS], t[DIMS],
    x_new[DIMS], delta_t_f, x_t_f[DIMS];
  charges[0][0] = 10.0;
  charges[0][1] = 10.0-w[0];
  charges[1][0] = 10.0;
  charges[1][1] = 0.0;
  x[0] = 0.0;
  x[1] = 8.0;
  xdot[0] = 0.75;
  xdot[1] = 0.0;
 loop:
  gradient(p, x, g);
  ktimesv(-1.0, g, xddot);
  ktimesv(delta_t, xdot, t);
  vplus(x, t, x_new);
  if (x_new[1]>0.0) {
    for (int j = 0; j<DIMS; j++) x[j] = x_new[j];
    ktimesv(delta_t, xddot, t);
    vplus(xdot, t, xdot);
    goto loop;}
  delta_t_f = -x[1]/xdot[1];
  ktimesv(delta_t_f, xdot, t);
  vplus(x, t, x_t_f);
  return x_t_f[0]*x_t_f[0];}

int main() {
  double w0[CONTROLS], w_star[CONTROLS];
  w0[0] = 0.0;
  multivariate_argmin(naive_euler, w0, w_star);
  cout<<setprecision(18)<<w_star[0]<<endl;
  return 0;}
