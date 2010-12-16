      subroutine f(x, r)
      include 'saddle-FF-adifor.inc'
      double precision x(4), r
      r = (x(1)*x(1)+x(2)*x(2))-(x(3)*x(3)+x(4)*x(4))
      end

      subroutine inner(x2, r)
      include 'saddle-FF-adifor.inc'
      double precision x2(ninner), r, x(ntotal), s, x1c(nouter)
      common /closure/ x1c
      x(1) = x1c(1)
      x(2) = x1c(2)
      x(3) = x2(1)
      x(4) = x2(2)
      call f(x, s)
      r = -s
      end
