int double_part(double x, int i)
{ union {double d; short s[4];} y;
  y.d = x;
  return y.s[i];}

double make_double(int s0, int s1, int s2, int s3)
{ union {double d; short s[4];} y;
  y.s[0] = s0;
  y.s[1] = s1;
  y.s[2] = s2;
  y.s[3] = s3;
  return y.d;}
