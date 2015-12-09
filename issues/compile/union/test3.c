
/* C program */

void test3_lin() {
  union {
    int u0;
    struct {
      int f0;
      int f1;
    } u1;
  } c_lin;
  c_lin.u0 = 1;
  const int x0_lin = c_lin.u0;
  c_lin.u1.f0 = x0_lin;
  c_lin.u1.f1 = x0_lin;
  const int y0_lin = c_lin.u1.f0;
  const int z0_lin = c_lin.u1.f1;
}
