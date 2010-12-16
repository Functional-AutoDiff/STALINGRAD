#include "backprop-Fv-adic-f.h"

double magnitude_squared(int n_x, double *x) {
  double r;
  r = 0.0;
  int j;
  for (j = 0; j<n_x; j++) r += x[j]*x[j];
  return r;}

void sum_layer_sigmoid(double *activities, int n_elements, int n_weights,
		       double *weights, double *out) {
  int i, j;
  for (i = 0; i<n_elements; i++) {
    out[i] = weights[i*n_weights];
    for (j = 0; j<n_weights-1; j++)
      out[i] += activities[j]*weights[i*n_weights+j+1];
    out[i] = 1.0/(exp(-1.0*out[i])+1.0);}}

void forward_pass(int n_ws_layers, double *ws_layers, int n_layers_format,
		  struct w_layer *layers_format, int n_in, double *in,
		  int n_out, double *out) {
  int i, j, count;
  double temp_in[ELEMENTS_LAYER_MAX];
  double temp_out[ELEMENTS_LAYER_MAX];
  double temp_weights[WEIGHTS_LAYER_MAX];
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

double error_on_dataset(int n_ws_layers, double *ws_layers,
			int n_layers_format, struct w_layer *layers_format) {
  double xor_data[N_SAMPLES][N_IN+N_OUT];
  int i, j;
  double error;
  double in[N_IN];
  double out[N_OUT], absolute_error[N_OUT];
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
