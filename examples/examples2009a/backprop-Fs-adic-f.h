#include <math.h>

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

double magnitude_squared(int n_x, double *x);
void sum_layer_sigmoid(double *activities, int n_elements, int n_weights,
		       double *weights, double *out);
void forward_pass(int n_ws_layers, double *ws_layers, int n_layers_format,
		  struct w_layer *layers_format, int n_in, double *in,
		  int n_out, double *out);
double error_on_dataset(int n_ws_layers, double *ws_layers,
			int n_layers_format, struct w_layer *layers_format);
