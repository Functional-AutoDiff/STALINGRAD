#include "fadiff.h"
#include <iomanip>
#include <math.h>
#include <stdlib.h>
using namespace std;

#define N_SAMPLES 4
#define N_IN 2
#define N_OUT 1
#define LAYERS 2
#define ELEMENTS_LAYER1 2
#define ELEMENTS_LAYER2 1
#define ELEMENTS_LAYER_MAX 2
#define WEIGHTS 3

struct w_layer {
  int n;
  int w;
  F<double> **layer;};

F<double> magnitude_squared(int n_x, F<double> *x) {
  F<double> r = 0.0;
  int j;
  for (j = 0; j<n_x; j++) r += x[j]*x[j];
  return r;}

void sum_layer_sigmoid(F<double> *activities, struct w_layer ws_layer,
		       F<double> *out) {
  int i, j;
  for (i = 0; i<ws_layer.n; i++) {
    out[i] = ws_layer.layer[i][0];
    for (j = 0; j<ws_layer.w-1; j++)
      out[i] += activities[j]*ws_layer.layer[i][j+1];
    out[i] = 1.0/(exp(-1.0*out[i])+1.0);}}

void forward_pass(int n_ws_layers, struct w_layer *ws_layers, int n_in,
		  F<double> *in, int n_out, F<double> *out) {
  int i, j;
  F<double> temp_in[ELEMENTS_LAYER_MAX];
  F<double> temp_out[ELEMENTS_LAYER_MAX];
  for (i = 0; i<n_in; i++) temp_in[i] = in[i];
  for (i = 0; i<n_ws_layers; i++) {
    sum_layer_sigmoid(&temp_in[0], ws_layers[i], &temp_out[0]);
    for (j = 0; j<ws_layers[i].n; j++) temp_in[j] = temp_out[j];}
  for (i = 0; i<n_out; i++) out[i] = temp_out[i];}

F<double> error_on_dataset(int n_ws_layers, struct w_layer *ws_layers) {
  F<double> xor_data[N_SAMPLES][N_IN+N_OUT];
  int i, j;
  F<double> error;
  F<double> in[N_IN];
  F<double> out[N_OUT], absolute_error[N_OUT];
  xor_data[0][0] = 0.0;
  xor_data[0][1] = 0.0;
  xor_data[0][2] = 0.0;
  xor_data[1][0] = 0.0;
  xor_data[1][1] = 1.0;
  xor_data[1][2] = 1.0;
  xor_data[2][0] = 1.0;
  xor_data[2][1] = 0.0;
  xor_data[2][2] = 1.0;
  xor_data[3][0] = 1.0;
  xor_data[3][1] = 1.0;
  xor_data[3][2] = 0.0;
  error = 0.0;
  for (i = 0; i<N_SAMPLES; i++) {
    for (j = 0; j<N_IN; j++) in[j] = xor_data[i][j];
    forward_pass(n_ws_layers, ws_layers, N_IN, &in[0], N_OUT, &out[0]);
    for (j = 0; j<N_OUT; j++) absolute_error[j] = out[j]-xor_data[i][j+N_IN];
    error += 0.5*magnitude_squared(N_OUT, &absolute_error[0]);}
  return error;}

void weight_gradient(F<double> f(int, struct w_layer *), int n_ws_layers,
		     struct w_layer *ws_layers, struct w_layer *grad_f) {
  int i, j, k, n, count;
  F<double> result;
  n = 0;
  for (i = 0; i<n_ws_layers; i++) n += ws_layers[i].n*ws_layers[i].w;
  count = 0;
  for (i = 0; i<n_ws_layers; i++) {
    for (j = 0; j<ws_layers[i].n; j++) {
      for (k = 0; k<ws_layers[i].w; k++) {
        ws_layers[i].layer[j][k].diff(count, n);
	count++;}}}
  result = f(n_ws_layers, ws_layers);
  count = 0;
  for (i = 0; i<n_ws_layers; i++) {
    for (j = 0; j<ws_layers[i].n; j++) {
      for (k = 0; k<ws_layers[i].w; k++) {
        grad_f[i].layer[j][k] = result.d(count);
	count++;}}}}

void vanilla(F<double> f(int, struct w_layer *), int n_w0, struct w_layer *w0,
	     int n, double eta) {
  int i, j, k, l;
  struct w_layer grad_f[n_w0];
  for (i = 0; i<n_w0; i++) {
    grad_f[i].n = w0[i].n;
    grad_f[i].w = w0[i].w;
    grad_f[i].layer = new F<double> * [grad_f[i].n];
    for (j = 0; j<grad_f[i].n; j++)
      grad_f[i].layer[j] = new F<double> [grad_f[i].w];}
  for (i = 0; i<n; i++) {
    weight_gradient(f, n_w0, w0, &grad_f[0]);
    for (j = 0; j<n_w0; j++)
      for (k = 0; k<w0[j].n; k++)
        for (l = 0; l<w0[j].w; l++)
	  w0[j].layer[k][l] =
	    w0[j].layer[k][l].x()-eta*grad_f[j].layer[k][l].x();}
  for (i = 0; i<n_w0; i++) {
    for (j = 0; j<grad_f[i].n; j++) delete[] grad_f[i].layer[j];
    delete[] grad_f[i].layer;}}

int main() {
  int i, j;
  struct w_layer xor_ws0[LAYERS];
  F<double> error;
  xor_ws0[0].n = ELEMENTS_LAYER1;
  xor_ws0[1].n = ELEMENTS_LAYER2;
  xor_ws0[0].w = WEIGHTS;
  xor_ws0[1].w = WEIGHTS;
  for (i = 0; i<LAYERS; i++) {
    xor_ws0[i].layer = new F<double> * [xor_ws0[i].n];
    for (j = 0; j<xor_ws0[i].n; j++)
      xor_ws0[i].layer[j] = new F<double> [xor_ws0[i].w];}
  xor_ws0[0].layer[0][0] = 0.0;
  xor_ws0[0].layer[0][1] = -0.284227;
  xor_ws0[0].layer[0][2] = 1.16054;
  xor_ws0[0].layer[1][0] = 0.0;
  xor_ws0[0].layer[1][1] = 0.617194;
  xor_ws0[0].layer[1][2] = 1.30467;
  xor_ws0[1].layer[0][0] = 0.0;
  xor_ws0[1].layer[0][1] = -0.084395;
  xor_ws0[1].layer[0][2] = 0.648461;
  vanilla(error_on_dataset, LAYERS, xor_ws0, 1000000, 0.3);
  error = error_on_dataset(LAYERS, xor_ws0);
  for (i = 0; i<LAYERS; i++) {
    for (j = 0; j<xor_ws0[i].n; j++) delete[] xor_ws0[i].layer[j];
    delete[] xor_ws0[i].layer;}
  cout << setprecision(18) << error.x() << endl;
  return EXIT_SUCCESS;}
