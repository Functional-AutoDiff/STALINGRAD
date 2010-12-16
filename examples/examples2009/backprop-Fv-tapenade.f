      subroutine vanilla(n_w0, w0, n_w0_format, w0_format, n, eta)
        integer n_w0, n_w0_format, n, i, j, k
        double precision w0(n_w0), eta, error
        integer w0_format(n_w0_format, 2)
        double precision g_w0(n_w0, n_w0), grad_f(n_w0)
        do i = 1, n
          do j = 1, n_w0
            do k = 1, n_w0
              if (j .eq. k) then
                g_w0(j, k) = 1d0
              else
                g_w0(j, k) = 0d0
              endif
            enddo
          enddo
          call error_on_dataset_dv(n_w0, w0, g_w0, n_w0_format,
     *      w0_format, error, grad_f, n_w0)
          do j = 1, n_w0
            w0(j) = w0(j)-eta*grad_f(j)
          enddo
        enddo
        call error_on_dataset_dv(n_w0, w0, g_w0, n_w0_format,
     *    w0_format, error, grad_f, n_w0)
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
