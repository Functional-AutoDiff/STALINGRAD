      subroutine magnitude_squared(n_x, x, r)
        integer n_x, j
        double precision x(n_x), r
        r = 0d0
        do j = 1, n_x
          r = r+x(j)*x(j)
        enddo
      end

      subroutine sum_layer_sigmoid(activities, n_elements, n_weights,
     * weights, out)
        integer i, j, n_elements, n_weights
        double precision activities(n_weights-1)
        double precision weights(n_elements*n_weights)
        double precision out(n_elements)
        do i = 1, n_elements
          out(i) = weights((i-1)*n_weights+1)
          do j = 1, n_weights-1
            out(i) = out(i)+activities(j)*weights((i-1)*n_weights+j+1)
          enddo
          out(i) = 1d0/(exp(-1d0*out(i))+1d0)
        enddo
      end

      subroutine forward_pass(n_ws_layers, ws_layers, n_layers_format,
     * layers_format, n_in, in, n_out, out)
        integer i, j, count, n_ws_layers, n_layers_format, n_in, n_out
        double precision ws_layers(n_ws_layers), in(n_in), out(n_out)
        integer layers_format(n_layers_format, 2)
        double precision temp_weights(6), temp_in(2), temp_out(2)
        count = 1
        do i = 1, n_in
          temp_in(i) = in(i)
        enddo
        do i = 1, n_layers_format
          do j = 1, layers_format(i, 1)*layers_format(i, 2)
            temp_weights(j) = ws_layers(count)
            count = count+1
          enddo
          call sum_layer_sigmoid(temp_in, layers_format(i, 1),
     *     layers_format(i, 2), temp_weights, temp_out)
          do j = 1, layers_format(i, 1)
            temp_in(j) = temp_out(j)
          enddo
        enddo
        do i = 1, n_out
          out(i) = temp_out(i)
        enddo
      end

      subroutine error_on_dataset(n_ws_layers, ws_layers,
     * n_layers_format, layers_format, error)
        integer i, j, n_ws_layers, n_layers_format
        double precision ws_layers(n_ws_layers), xor_data(4, 3)
        integer layers_format(n_layers_format, 2)
        double precision in(2), out(1), absolute_error(1), mag, error
        xor_data(1, 1) = 0d0
        xor_data(1, 2) = 0d0
        xor_data(1, 3) = 0d0
        xor_data(2, 1) = 0d0
        xor_data(2, 2) = 1d0
        xor_data(2, 3) = 1d0
        xor_data(3, 1) = 1d0
        xor_data(3, 2) = 0d0
        xor_data(3, 3) = 1d0
        xor_data(4, 1) = 1d0
        xor_data(4, 2) = 1d0
        xor_data(4, 3) = 0d0
        error = 0d0
        do i = 1, 4
          do j = 1, 2
            in(j) = xor_data(i, j)
          enddo
          call forward_pass(n_ws_layers, ws_layers, n_layers_format,
     *     layers_format, 2, in, 1, out)
          do j = 1, 1
            absolute_error(j) = out(j)-xor_data(i, j+2)
          enddo
          call magnitude_squared(1, absolute_error, mag)
          error = error+0.5d0*mag
        enddo
      end
