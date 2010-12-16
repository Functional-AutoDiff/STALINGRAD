#include <stdio.h>
#include <stdlib.h>
#include "ad_deriv.h"
#include "backprop-Fs-adic-f.ad.c"

#define N_SAMPLES 4
#define N_IN 2
#define N_OUT 1
#define LAYERS 2
#define ELEMENTS_LAYER1 2
#define ELEMENTS_LAYER2 1
#define ELEMENTS_LAYER_MAX 2
#define WEIGHTS_LAYER_MAX 6
#define WEIGHTS 3

void vanilla(int n_w0, DERIV_TYPE *w0, int n_layers, struct w_layer *w0_format,
	     int n, double eta) {
  int i, j, j1;
  DERIV_TYPE y;
  double *grad_f, zero[1], one[1];
  zero[0] = 0.0;
  one[0] = 1.0;
  grad_f = (double *) malloc(n_w0*sizeof(double));
  for (i = 0; i<n; i++) {
    for (j = 0; j<n_w0; j++) {
      for (j1 = 0; j1<n_w0; j1++)
	ad_AD_SetGrad(((j==j1)?(&one[0]):(&zero[0])), w0[j1]);
      ad_error_on_dataset(&y, n_w0, w0, n_layers, w0_format);
      ad_AD_ExtractGrad(&grad_f[j], y);}
    for (j = 0; j<n_w0; j++)
      DERIV_val(w0[j]) = DERIV_val(w0[j])-eta*grad_f[j];}
  free(grad_f);}

int main(void) {
  int i, n_xor_ws0;
  DERIV_TYPE *xor_ws0, y;
  double error;
  struct w_layer xor_ws0_format[LAYERS];
  xor_ws0_format[0].n = ELEMENTS_LAYER1;
  xor_ws0_format[1].n = ELEMENTS_LAYER2;
  xor_ws0_format[0].w = WEIGHTS;
  xor_ws0_format[1].w = WEIGHTS;
  n_xor_ws0 = 0;
  for (i = 0; i<LAYERS; i++)
    n_xor_ws0 += xor_ws0_format[i].n*xor_ws0_format[i].w;
  xor_ws0 = (DERIV_TYPE *) malloc(n_xor_ws0*sizeof(DERIV_TYPE));
  ad_AD_SetIndep(xor_ws0[0]);
  ad_AD_SetIndepDone();
  DERIV_val(xor_ws0[0]) = 0.0;
  DERIV_val(xor_ws0[1]) = -0.284227;
  DERIV_val(xor_ws0[2]) = 1.16054;
  DERIV_val(xor_ws0[3]) = 0.0;
  DERIV_val(xor_ws0[4]) = 0.617194;
  DERIV_val(xor_ws0[5]) = 1.30467;
  DERIV_val(xor_ws0[6]) = 0.0;
  DERIV_val(xor_ws0[7]) = -0.084395;
  DERIV_val(xor_ws0[8]) = 0.648461;
  vanilla(n_xor_ws0, xor_ws0, LAYERS, &xor_ws0_format[0], 1000000, 0.3);
  ad_error_on_dataset(&y, n_xor_ws0, xor_ws0, LAYERS, &xor_ws0_format[0]);
  ad_AD_ExtractVal(error, y);
  printf("%.18lg\n", error);
  free(xor_ws0);
  return 0;}
