      subroutine p(x, r)
      include 'particle-FF-tapenade.inc'
      double precision x(dims), r, charge(dims), s
      double precision charges(ncharges, dims)
      common /closure/ charges
      integer k, l
      r = 0d0
      do l = 1, ncharges
         do k = 1, dims
            charge(k) = charges(l, k)
         enddo
         call distance(dims, x, charge, s)
         r = r+1d0/s
      enddo
      end

      subroutine gradient_p(x, g)
      include 'particle-FF-tapenade.inc'
      double precision x(dims), g(dims), g_x(dims, dims), y
      integer k, l
      do k = 1, dims
         do l = 1, dims
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call p_gv(x, g_x, y, g, dims)
      end

      subroutine naive_euler(w, r)
      include 'particle-FF-tapenade.inc'
      double precision w(controls), r
      double precision x(dims), xdot(dims), delta_t, g(dims)
      double precision xddot(dims), t(dims), x_new(dims), s(dims)
      double precision delta_t_f, x_t_f(dims), charges(ncharges, dims)
      double precision charges_g(dims, ncharges, dims)
      common /closure/ charges
      common /closure_gv/ charges_g
      integer j
      delta_t = 1e-1
      charges(1, 1) = 10d0
      charges(1, 2) = 10d0-w(1)
      charges(2, 1) = 10d0
      charges(2, 2) = 0d0
      do j = 1, dims
         charges_g(dims, 1, 1) = 0d0
         charges_g(dims, 1, 2) = 0d0
         charges_g(dims, 2, 1) = 0d0
         charges_g(dims, 2, 2) = 0d0
      enddo
      x(1) = 0d0
      x(2) = 8d0
      xdot(1) = 0.75d0
      xdot(2) = 0d0
 1    call gradient_p(x, g)
      call ktimesv(dims, -1d0, g, xddot)
      call ktimesv(dims, delta_t, xdot, t)
      call vplus(dims, x, t, x_new)
      if (x_new(2).gt.0d0) then
         do j = 1, dims
            x(j) = x_new(j)
         enddo
         call ktimesv(dims, delta_t, xddot, t)
         call vplus(dims, xdot, t, s)
         do j = 1, dims
            xdot(j) = s(j)
         enddo
         goto 1
      endif
      delta_t_f = -x(2)/xdot(2)
      call ktimesv(dims, delta_t_f, xdot, t)
      call vplus(dims, x, t, x_t_f)
      r = x_t_f(1)*x_t_f(1)
      end

      subroutine gradient_naive_euler(x, g)
      include 'particle-FF-tapenade.inc'
      double precision x(controls), g(controls)
      double precision g_x(controls, controls), y
      integer k, l
      do k = 1, controls
         do l = 1, controls
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call naive_euler_hv(x, g_x, y, g, controls)
      end

      program main
      include 'particle-FF-tapenade.inc'
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
