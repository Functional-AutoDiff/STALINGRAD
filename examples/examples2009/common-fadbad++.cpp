#include "fadiff.h"
using namespace std;

template <typename D_u, typename D_v, typename D_r, int n>
void vplus(D_u (&u)[n], D_v (&v)[n], D_r (&r)[n]) {
  for (int j = 0; j<n; j++) r[j] = u[j]+v[j];}

template <typename D_u, typename D_v, typename D_r, int n>
void vminus(D_u (&u)[n], D_v (&v)[n], D_r (&r)[n]) {
  for (int j = 0; j<n; j++) r[j] = u[j]-v[j];}

template <typename D_k, typename D_v, typename D_r, int n>
void ktimesv(D_k k, D_v (&v)[n], D_r (&r)[n]) {
  for (int j = 0; j<n; j++) r[j] = k*v[j];}

template <typename D, int n>
D magnitude_squared(D (&x)[n]) {
  D r = 0.0;
  for (int j = 0; j<n; j++) r += x[j]*x[j];
  return r;}

template <typename D, int n>
D magnitude(D (&x)[n]) {return sqrt(magnitude_squared(x));}

template <typename D, int n>
D distance_squared(D (&u)[n], D (&v)[n]) {
  D t[n];
  vminus(u, v, t);
  return magnitude_squared(t);}

template <typename D, int n>
D distance(D (&u)[n], D (&v)[n]) {
  return sqrt(distance_squared(u, v));}

template <typename D, int n>
D gradient(F<D> f(F<D> (&)[n]), D (&x)[n], D (&f_gradient)[n]) {
  F<D> g_x[n], y;
  for (int k = 0; k<n; k++) {
    g_x[k] = x[k];
    g_x[k].diff(k, n);}
  y = f(g_x);
  for (int k = 0; k<n; k++) f_gradient[k] = y.d(k);
  return y.x();}

template <typename D, int n>
D multivariate_argmin(F<D> f(F<D> (&)[n]), D (&x)[n], D (&x_star)[n]) {
  D fx, gx[n], eta = 1e-5, t[n], x_prime[n], fx_prime;
  int i = 0;
  fx = gradient(f, x, gx);
  for (int j = 0; j<n; j++) {x_star[j] = x[j];}
 loop:
  if (magnitude(gx)<=1e-5) return fx;
  if (i==10) {eta *= 2.0; i = 0; goto loop;}
  ktimesv(eta, gx, t);
  vminus(x_star, t, x_prime);
  if (distance(x_star, x_prime)<=1e-5) return fx;
  fx_prime = gradient(f, x_prime, gx);
  if (fx_prime<fx) {
    for (int j = 0; j<n; j++) x_star[j] = x_prime[j];
    fx = fx_prime;
    i++;
    goto loop;}
  eta /= 2.0;
  i = 0;
  goto loop;}
