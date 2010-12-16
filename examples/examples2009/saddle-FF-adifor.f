      subroutine gradient_outer(x, g)
      include 'saddle-FF-adifor.inc'
      double precision x(nouter), g(nouter), g_x(nouter, nouter), y
      integer k, l
      do k = 1, nouter
         do l = 1, nouter
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call h_outer(x, g_x, y, g)
      end

      program main
      include 'saddle-FF-adifor.inc'
      double precision x1_start(nouter), x2_start(ninner)
      double precision x1_star(nouter), x2_star(ninner), r
      double precision x1c(nouter), g_x1c(ninner, nouter)
      common /closure/ x1c
      common /g_closure/ g_x1c
      integer i, k
      external outer, gradient_outer, inner, gradient_inner
      do i = 1, 1000
         x1_start(1) = 1d0
         x1_start(2) = 1d0
         x2_start(1) = 1d0
         x2_start(2) = 1d0
         call multivariate_argmin
     +        (nouter, outer, gradient_outer, x1_start, x1_star, r)
         x1c(1) = x1_star(1)
         x1c(2) = x1_star(2)
         do k = 1, ninner
            g_x1c(k, 1) = 0d0
            g_x1c(k, 2) = 0d0
         enddo
         call multivariate_argmin
     +        (ninner, inner, gradient_inner, x2_start, x2_star, r)
         print *, x1_star(1), x1_star(2), x2_star(1), x2_star(2)
      enddo
      end
