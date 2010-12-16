      subroutine gradient_inner(x, g)
      include 'saddle-FF-adifor.inc'
      double precision x(ninner), g(ninner), g_x(ninner, ninner), y
      integer k, l
      do k = 1, ninner
         do l = 1, ninner
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call g_inner(x, g_x, y, g)
      end

      subroutine outer(x1, r)
      include 'saddle-FF-adifor.inc'
      double precision x1(nouter), r, x2(ninner), x2_star(ninner), s
      double precision x1c(nouter), g_x1c(ninner, nouter)
      common /closure/ x1c
      common /g_closure/ g_x1c
      integer k
      external inner, gradient_inner
      x1c(1) = x1(1)
      x1c(2) = x1(2)
      do k = 1, ninner
         g_x1c(k, 1) = 0d0
         g_x1c(k, 2) = 0d0
      enddo
      x2(1) = 1d0
      x2(2) = 1d0
      call multivariate_argmin
     +     (ninner, inner, gradient_inner, x2, x2_star, s)
      r = -s
      end
