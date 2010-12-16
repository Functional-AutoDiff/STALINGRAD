      subroutine vplus(n, u, v, r)
      integer n, j
      double precision u(n), v(n), r(n)
      do j = 1, n
         r(j) = u(j)+v(j)
      enddo
      end

      subroutine vminus(n, u, v, r)
      integer n, j
      double precision u(n), v(n), r(n)
      do j = 1, n
         r(j) = u(j)-v(j)
      enddo
      end

      subroutine ktimesv(n, k, v, r)
      integer n, j
      double precision k, v(n), r(n)
      do j = 1, n
         r(j) = k*v(j)
      enddo
      end

      subroutine magnitude_squared(n, x, r)
      integer n, j
      double precision x(n), r
      r = 0d0
      do j = 1, n
         r = r+x(j)*x(j)
      enddo
      end

      subroutine magnitude(n, x, r)
      integer n
      double precision x(n), r, s
      call magnitude_squared(n, x, s)
      r = sqrt(s)
      end

      subroutine distance_squared(n, u, v, r)
      include 'common-adifor.inc'
      integer n
      double precision u(n), v(n), r, t(size)
C     need to enforce n<=size
      call vminus(n, u, v, t)
      call magnitude_squared(n, t, r)
      end

      subroutine distance(n, u, v, r)
      integer n
      double precision u(n), v(n), r, s
      call distance_squared(n, u, v, s)
      r = sqrt(s)
      end

      subroutine multivariate_argmin(n, f, g, x, x_star, fx)
      include 'common-adifor.inc'
      integer n, i, j
      double precision x(n), x_star(n), fx
      double precision gx(size), eta, t(size), x_prime(size), fx_prime
      double precision s
      external f, g
C     need to enforce n<=size
      call f(x, fx)
      eta = 1d-5
      i = 0
      do j = 1, n
         x_star(j) = x(j)
      enddo
      call g(x, gx)
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
      call f(x_prime, fx_prime)
      if (fx_prime.lt.fx) then
         do j = 1, n
            x_star(j) = x_prime(j)
         enddo
         fx = fx_prime
         call g(x_prime, gx)
         i = i+1
         goto 1
      endif
      eta = eta/2d0
      i = 0
      goto 1
      end
