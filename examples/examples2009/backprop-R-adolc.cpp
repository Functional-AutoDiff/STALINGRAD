#include "adolc/adouble.h"
#include "adolc/drivers/drivers.h"
#include <iomanip>
#include <math.h>
using namespace std;

#define N_SAMPLES 4
#define N_IN 2
#define N_OUT 1
#define LAYERS 2
#define ELEMENTS_LAYER1 2
#define ELEMENTS_LAYER2 1
#define ELEMENTS_LAYER_MAX 2
#define WEIGHTS_LAYER_MAX 6
#define WEIGHTS 3

struct w_layer {
  int n;
  int w;};

adouble magnitude_squared(int n_x, adouble *x) {
  adouble r;
  r = 0.0;
  int j;
  for (j = 0; j<n_x; j++) r += x[j]*x[j];
  return r;}

void sum_layer_sigmoid(adouble *activities, int n_elements, int n_weights,
		       adouble *weights, adouble *out) {
  int i, j;
  for (i = 0; i<n_elements; i++) {
    out[i] = weights[i*n_weights];
    for (j = 0; j<n_weights-1; j++) {
      out[i] += activities[j]*weights[i*n_weights+j+1];}
    out[i] = 1.0/(exp(-1.0*out[i])+1.0);}}

void forward_pass(int n_ws_layers, adouble *ws_layers, int n_layers_format,
		  struct w_layer *layers_format, int n_in, adouble *in,
		  int n_out, adouble *out) {
  int i, j, count;
  adouble temp_in[ELEMENTS_LAYER_MAX];
  adouble temp_out[ELEMENTS_LAYER_MAX];
  adouble temp_weights[WEIGHTS_LAYER_MAX];
  count = 0;
  for (i = 0; i<n_in; i++) temp_in[i] = in[i];
  for (i = 0; i<n_layers_format; i++) {
    for (j = 0; j<layers_format[i].n*layers_format[i].w; j++){
      temp_weights[j] = ws_layers[count];
      count++;}
    sum_layer_sigmoid(&temp_in[0], layers_format[i].n, layers_format[i].w,
      &temp_weights[0], &temp_out[0]);
    for (j = 0; j<layers_format[i].n; j++) temp_in[j] = temp_out[j];}
  for (i = 0; i<n_out; i++) out[i] = temp_out[i];}

adouble error_on_dataset(int n_ws_layers, adouble *ws_layers,
			 int n_layers_format, struct w_layer *layers_format) {
  double xor_data[N_SAMPLES][N_IN+N_OUT];
  int i, j;
  adouble error;
  adouble in[N_IN];
  adouble out[N_OUT], absolute_error[N_OUT];
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
    forward_pass(n_ws_layers, ws_layers, n_layers_format, layers_format, N_IN,
      &in[0], N_OUT, &out[0]);
    for (j = 0; j<N_OUT; j++) absolute_error[j] = out[j]-xor_data[i][j+N_IN];
    error += 0.5*magnitude_squared(N_OUT, &absolute_error[0]);}
  return error;}

void vanilla(int n_w0, double *w0_p, int n_layers, struct w_layer *w0_format,
	     int n, double eta) {
  int i, j;
  adouble *w0;
  w0 = new adouble[n_w0];
  adouble error;
  double error_p;
  double *grad_f;
  grad_f = new double[n_w0];
  for (i = 0; i<n; i++) {
    trace_on(1);
    for (j = 0; j<n_w0; j++) w0[j] <<= w0_p[j];
    error = error_on_dataset(n_w0, w0, n_layers, w0_format);
    error >>= error_p;
    trace_off();
    gradient(1, n_w0, w0_p, grad_f);
    for (j = 0; j<n_w0; j++) w0_p[j] = w0_p[j]-eta*grad_f[j];}
  for (j = 0; j<n_w0; j++) w0[j] <<= w0_p[j];
  error = error_on_dataset(n_w0, w0, n_layers, w0_format);
  error >>= error_p;
  cout << setprecision(18) << error_p << endl;
  delete[] w0;
  delete[] grad_f;}

int main() {
  int i, j, n_xor_ws0;
  struct w_layer xor_ws0_format[LAYERS];
  xor_ws0_format[0].n = ELEMENTS_LAYER1;
  xor_ws0_format[1].n = ELEMENTS_LAYER2;
  xor_ws0_format[0].w = WEIGHTS;
  xor_ws0_format[1].w = WEIGHTS;
  n_xor_ws0 = 0;
  for (i = 0; i<LAYERS; i++) {
    n_xor_ws0 += xor_ws0_format[i].n*xor_ws0_format[i].w;}
  double *xor_ws0_p;
  xor_ws0_p = new double[n_xor_ws0];
  xor_ws0_p[0] = 0.0;
  xor_ws0_p[1] = -0.284227;
  xor_ws0_p[2] = 1.16054;
  xor_ws0_p[3] = 0.0;
  xor_ws0_p[4] = 0.617194;
  xor_ws0_p[5] = 1.30467;
  xor_ws0_p[6] = 0.0;
  xor_ws0_p[7] = -0.084395;
  xor_ws0_p[8] = 0.648461;
  vanilla(n_xor_ws0, xor_ws0_p, LAYERS, &xor_ws0_format[0], 1000000, 0.3);
  delete[] xor_ws0_p;
  return EXIT_SUCCESS;}
