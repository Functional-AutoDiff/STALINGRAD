      subroutine gradient_naive_euler(x, g)
      include 'particle-FF-adifor.inc'
      double precision x(controls), g(controls)
      double precision g_x(controls, controls), y
      integer k, l
      do k = 1, controls
         do l = 1, controls
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call h_naive_euler(x, g_x, y, g)
      end

      program main
      include 'particle-FF-adifor.inc'
      double precision w0(controls), w_star(controls), r
      external naive_euler, gradient_naive_euler
      integer i
      do i = 1, 1000
         w0(1) = 0d0
         call multivariate_argmin
     +   (controls, naive_euler, gradient_naive_euler, w0, w_star, r)
         print *, w_star(1)
      enddo
      end
