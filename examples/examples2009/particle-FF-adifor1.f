      subroutine p(x, r)
      include 'particle-FF-adifor.inc'
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
