      subroutine gradient_p(x, g)
      include 'particle-FF-adifor.inc'
      double precision x(dims), g(dims), g_x(dims, dims), y
      integer k, l
      do k = 1, dims
         do l = 1, dims
            g_x(k, l) = 0d0
         enddo
         g_x(k, k) = 1d0
      enddo
      call g_p(x, g_x, y, g)
      end

      subroutine naive_euler(w, r)
      include 'particle-FF-adifor.inc'
      double precision w(controls), r
      double precision x(dims), xdot(dims), delta_t, g(dims)
      double precision xddot(dims), t(dims), x_new(dims), s(dims)
      double precision delta_t_f, x_t_f(dims), charges(ncharges, dims)
      double precision g_charges(dims, ncharges, dims)
      common /closure/ charges
      common /g_closure/ g_charges
      integer j
      delta_t = 1e-1
      charges(1, 1) = 10d0
      charges(1, 2) = 10d0-w(1)
      charges(2, 1) = 10d0
      charges(2, 2) = 0d0
      do j = 1, dims
         g_charges(dims, 1, 1) = 0d0
         g_charges(dims, 1, 2) = 0d0
         g_charges(dims, 2, 1) = 0d0
         g_charges(dims, 2, 2) = 0d0
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
