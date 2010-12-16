      subroutine vanilla(n_w0, w0, n_w0_format, w0_format, n, eta)
        integer n_w0, n_w0_format, n, i, j
        double precision w0(n_w0), eta, error
        integer w0_format(n_w0_format, 2)
        double precision error_h, grad_f(n_w0)
        do i = 1, n
          error_h = 1d0
          error = 0d0
          do j = 1, n_w0
            grad_f(j) = 0d0
          enddo
          call error_on_dataset_b(n_w0, w0, grad_f, 2, w0_format, error,
     *      error_h)
          do j = 1, n_w0
            w0(j) = w0(j)-eta*grad_f(j)
          enddo
        enddo
        call error_on_dataset(9, w0, 2, w0_format, error)
        print *, error
      end

      program driver
        double precision w0(9)
        integer w0_format(2, 2)
        w0(1) = 0d0
        w0(2) = -0.284227d0
        w0(3) = 1.16054d0
        w0(4) = 0d0
        w0(5) = 0.617194d0
        w0(6) = 1.30467d0
        w0(7) = 0d0
        w0(8) = -0.084395d0
        w0(9) = 0.648461d0
        w0_format(1, 1) = 2
        w0_format(1, 2) = 3
        w0_format(2, 1) = 1
        w0_format(2, 2) = 3
        call vanilla (9, w0, 2, w0_format, 1000000, 0.3d0)
      end
