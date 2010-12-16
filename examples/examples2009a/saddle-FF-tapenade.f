      subroutine f(x, r)
      include 'saddle-FF-tapenade.inc'
      double precision x(4), r
      r = x(1)*x(1)+x(2)*x(2)-x(3)*x(3)-x(4)*x(4)
      end

      subroutine inner(x2, r)
      include 'saddle-FF-tapenade.inc'
      double precision x2(ninner), r, x(ntotal), s, x1c(nouter)
      common /closure/ x1c
      x(1) = x1c(1)
      x(2) = x1c(2)
      x(3) = x2(1)
      x(4) = x2(2)
      call f(x, s)
      r = -s
      end

      subroutine gradient_inner(x, g)
      include 'saddle-FF-tapenade.inc'
      double precision x(ninner), g(ninner), g_x(ninner, ninner), y
      integer k, l
      do k = 1, ninner
         do l = 1, ninner
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call inner_gv(x, g_x, y, g, ninner)
      end

      subroutine multivariate_argmin_inner(n, x, x_star, fx)
      include 'common-tapenade.inc'
      integer n, i, j
      double precision x(n), x_star(n), fx
      double precision gx(size), eta, t(size), x_prime(size), fx_prime
      double precision s
C     need to enforce n<=size
      call inner(x, fx)
      eta = 1d-5
      i = 0
      do j = 1, n
         x_star(j) = x(j)
      enddo
      call gradient_inner(x, gx)
 1    call magnitude(n, gx, s)
      if (s.le.1d-5) return
      if (i.eq.10) then
         eta = eta*2d0
         i = 0
         goto 1
      endif
      call ktimesv(n, eta, gx, t)
      call vminus(n, x_star, t, x_prime)
      call distance(n, x_star, x_prime, s)
      if (s.le.1d-5) return
      call inner(x_prime, fx_prime)
      if (fx_prime.lt.fx) then
         do j = 1, n
            x_star(j) = x_prime(j)
         enddo
         fx = fx_prime
         call gradient_inner(x_prime, gx)
         i = i+1
         goto 1
      endif
      eta = eta/2d0
      i = 0
      goto 1
      end

      subroutine outer(x1, r)
      include 'saddle-FF-tapenade.inc'
      double precision x1(nouter), r, x2(ninner), x2_star(ninner), s
      double precision x1c(nouter), x1c_g(ninner, nouter)
      common /closure/ x1c
      common /closure_gv/ x1c_g
      integer k
      x1c(1) = x1(1)
      x1c(2) = x1(2)
      do k = 1, ninner
         x1c_g(k, 1) = 0d0
         x1c_g(k, 2) = 0d0
      enddo
      x2(1) = 1d0
      x2(2) = 1d0
      call multivariate_argmin_inner(ninner, x2, x2_star, s)
      r = -s
      end

      subroutine gradient_outer(x, g)
      include 'saddle-FF-tapenade.inc'
      double precision x(nouter), g(nouter), g_x(nouter, nouter), y
      integer k, l
      do k = 1, nouter
         do l = 1, nouter
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call outer_hv(x, g_x, y, g, nouter)
      end

      program main
      include 'saddle-FF-tapenade.inc'
      double precision x1_start(nouter), x2_start(ninner)
      double precision x1_star(nouter), x2_star(ninner), r
      double precision x1c(nouter), x1c_g(ninner, nouter)
      common /closure/ x1c
      common /closure_gv/ x1c_g
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
            x1c_g(k, 1) = 0d0
            x1c_g(k, 2) = 0d0
         enddo
         call multivariate_argmin
     +        (ninner, inner, gradient_inner, x2_start, x2_star, r)
         print *, x1_star(1), x1_star(2), x2_star(1), x2_star(2)
      enddo
      end
