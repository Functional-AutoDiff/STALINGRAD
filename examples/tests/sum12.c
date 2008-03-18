#include <stdio.h>

#define INLINE inline __attribute__ ((always_inline))

struct pair0 {double left;double right;};
struct pair1 {struct pair0 left;struct pair0 right;};
struct pair2 {struct pair1 left;struct pair1 right;};
struct pair3 {struct pair2 left;struct pair2 right;};
struct pair4 {struct pair3 left;struct pair3 right;};
struct pair5 {struct pair4 left;struct pair4 right;};
struct pair6 {struct pair5 left;struct pair5 right;};
struct pair7 {struct pair6 left;struct pair6 right;};
struct pair8 {struct pair7 left;struct pair7 right;};
struct pair9 {struct pair8 left;struct pair8 right;};
struct pair10 {struct pair9 left;struct pair9 right;};
struct pair11 {struct pair10 left;struct pair10 right;};
struct pair12 {struct pair11 left;struct pair11 right;};
struct pair13 {struct pair12 left;struct pair12 right;};
struct pair14 {struct pair13 left;struct pair13 right;};
struct pair15 {struct pair14 left;struct pair14 right;};
struct pair16 {struct pair15 left;struct pair15 right;};
struct pair17 {struct pair16 left;struct pair16 right;};
struct pair18 {struct pair17 left;struct pair17 right;};
struct pair19 {struct pair18 left;struct pair18 right;};

static INLINE struct pair0 tree0(double x);
static INLINE struct pair1 tree1(struct pair0 x);
static INLINE struct pair2 tree2(struct pair1 x);
static INLINE struct pair3 tree3(struct pair2 x);
static INLINE struct pair4 tree4(struct pair3 x);
static INLINE struct pair5 tree5(struct pair4 x);
static INLINE struct pair6 tree6(struct pair5 x);
static INLINE struct pair7 tree7(struct pair6 x);
static INLINE struct pair8 tree8(struct pair7 x);
static INLINE struct pair9 tree9(struct pair8 x);
static INLINE struct pair10 tree10(struct pair9 x);
static INLINE struct pair11 tree11(struct pair10 x);
static INLINE struct pair12 tree12(struct pair11 x);
static INLINE struct pair13 tree13(struct pair12 x);
static INLINE struct pair14 tree14(struct pair13 x);
static INLINE struct pair15 tree15(struct pair14 x);
static INLINE struct pair16 tree16(struct pair15 x);
static INLINE struct pair17 tree17(struct pair16 x);
static INLINE struct pair18 tree18(struct pair17 x);
static INLINE struct pair19 tree19(struct pair18 x);
static INLINE struct pair0 swap0(struct pair0 x);
static INLINE struct pair1 swap1(struct pair1 x);
static INLINE struct pair2 swap2(struct pair2 x);
static INLINE struct pair3 swap3(struct pair3 x);
static INLINE struct pair4 swap4(struct pair4 x);
static INLINE struct pair5 swap5(struct pair5 x);
static INLINE struct pair6 swap6(struct pair6 x);
static INLINE struct pair7 swap7(struct pair7 x);
static INLINE struct pair8 swap8(struct pair8 x);
static INLINE struct pair9 swap9(struct pair9 x);
static INLINE struct pair10 swap10(struct pair10 x);
static INLINE struct pair11 swap11(struct pair11 x);
static INLINE struct pair12 swap12(struct pair12 x);
static INLINE struct pair13 swap13(struct pair13 x);
static INLINE struct pair14 swap14(struct pair14 x);
static INLINE struct pair15 swap15(struct pair15 x);
static INLINE struct pair16 swap16(struct pair16 x);
static INLINE struct pair17 swap17(struct pair17 x);
static INLINE struct pair18 swap18(struct pair18 x);
static INLINE struct pair19 swap19(struct pair19 x);
static INLINE double left0(struct pair0 x);
static INLINE struct pair0 left1(struct pair1 x);
static INLINE struct pair1 left2(struct pair2 x);
static INLINE struct pair2 left3(struct pair3 x);
static INLINE struct pair3 left4(struct pair4 x);
static INLINE struct pair4 left5(struct pair5 x);
static INLINE struct pair5 left6(struct pair6 x);
static INLINE struct pair6 left7(struct pair7 x);
static INLINE struct pair7 left8(struct pair8 x);
static INLINE struct pair8 left9(struct pair9 x);
static INLINE struct pair9 left10(struct pair10 x);
static INLINE struct pair10 left11(struct pair11 x);
static INLINE struct pair11 left12(struct pair12 x);
static INLINE struct pair12 left13(struct pair13 x);
static INLINE struct pair13 left14(struct pair14 x);
static INLINE struct pair14 left15(struct pair15 x);
static INLINE struct pair15 left16(struct pair16 x);
static INLINE struct pair16 left17(struct pair17 x);
static INLINE struct pair17 left18(struct pair18 x);
static INLINE struct pair18 left19(struct pair19 x);
static INLINE double right0(struct pair0 x);
static INLINE struct pair0 right1(struct pair1 x);
static INLINE struct pair1 right2(struct pair2 x);
static INLINE struct pair2 right3(struct pair3 x);
static INLINE struct pair3 right4(struct pair4 x);
static INLINE struct pair4 right5(struct pair5 x);
static INLINE struct pair5 right6(struct pair6 x);
static INLINE struct pair6 right7(struct pair7 x);
static INLINE struct pair7 right8(struct pair8 x);
static INLINE struct pair8 right9(struct pair9 x);
static INLINE struct pair9 right10(struct pair10 x);
static INLINE struct pair10 right11(struct pair11 x);
static INLINE struct pair11 right12(struct pair12 x);
static INLINE struct pair12 right13(struct pair13 x);
static INLINE struct pair13 right14(struct pair14 x);
static INLINE struct pair14 right15(struct pair15 x);
static INLINE struct pair15 right16(struct pair16 x);
static INLINE struct pair16 right17(struct pair17 x);
static INLINE struct pair17 right18(struct pair18 x);
static INLINE struct pair18 right19(struct pair19 x);
static INLINE double sum(struct pair11 x);
static double read_real(void);
int main(void);

static INLINE struct pair0 tree0(double x) {
  struct pair0 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair1 tree1(struct pair0 x) {
  struct pair1 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair2 tree2(struct pair1 x) {
  struct pair2 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair3 tree3(struct pair2 x) {
  struct pair3 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair4 tree4(struct pair3 x) {
  struct pair4 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair5 tree5(struct pair4 x) {
  struct pair5 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair6 tree6(struct pair5 x) {
  struct pair6 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair7 tree7(struct pair6 x) {
  struct pair7 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair8 tree8(struct pair7 x) {
  struct pair8 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair9 tree9(struct pair8 x) {
  struct pair9 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair10 tree10(struct pair9 x) {
  struct pair10 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair11 tree11(struct pair10 x) {
  struct pair11 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair12 tree12(struct pair11 x) {
  struct pair12 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair13 tree13(struct pair12 x) {
  struct pair13 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair14 tree14(struct pair13 x) {
  struct pair14 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair15 tree15(struct pair14 x) {
  struct pair15 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair16 tree16(struct pair15 x) {
  struct pair16 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair17 tree17(struct pair16 x) {
  struct pair17 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair18 tree18(struct pair17 x) {
  struct pair18 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair19 tree19(struct pair18 x) {
  struct pair19 result;
  result.left=x;
  result.right=x;
  return result;}

static INLINE struct pair0 swap0(struct pair0 x) {
  struct pair0 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair1 swap1(struct pair1 x) {
  struct pair1 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair2 swap2(struct pair2 x) {
  struct pair2 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair3 swap3(struct pair3 x) {
  struct pair3 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair4 swap4(struct pair4 x) {
  struct pair4 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair5 swap5(struct pair5 x) {
  struct pair5 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair6 swap6(struct pair6 x) {
  struct pair6 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair7 swap7(struct pair7 x) {
  struct pair7 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair8 swap8(struct pair8 x) {
  struct pair8 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair9 swap9(struct pair9 x) {
  struct pair9 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair10 swap10(struct pair10 x) {
  struct pair10 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair11 swap11(struct pair11 x) {
  struct pair11 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair12 swap12(struct pair12 x) {
  struct pair12 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair13 swap13(struct pair13 x) {
  struct pair13 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair14 swap14(struct pair14 x) {
  struct pair14 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair15 swap15(struct pair15 x) {
  struct pair15 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair16 swap16(struct pair16 x) {
  struct pair16 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair17 swap17(struct pair17 x) {
  struct pair17 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair18 swap18(struct pair18 x) {
  struct pair18 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE struct pair19 swap19(struct pair19 x) {
  struct pair19 result;
  result.left = x.right;
  result.right = x.left;
  return result;}

static INLINE double left0(struct pair0 x) {return x.left;}
static INLINE struct pair0 left1(struct pair1 x) {return x.left;}
static INLINE struct pair1 left2(struct pair2 x) {return x.left;}
static INLINE struct pair2 left3(struct pair3 x) {return x.left;}
static INLINE struct pair3 left4(struct pair4 x) {return x.left;}
static INLINE struct pair4 left5(struct pair5 x) {return x.left;}
static INLINE struct pair5 left6(struct pair6 x) {return x.left;}
static INLINE struct pair6 left7(struct pair7 x) {return x.left;}
static INLINE struct pair7 left8(struct pair8 x) {return x.left;}
static INLINE struct pair8 left9(struct pair9 x) {return x.left;}
static INLINE struct pair9 left10(struct pair10 x) {return x.left;}
static INLINE struct pair10 left11(struct pair11 x) {return x.left;}
static INLINE struct pair11 left12(struct pair12 x) {return x.left;}
static INLINE struct pair12 left13(struct pair13 x) {return x.left;}
static INLINE struct pair13 left14(struct pair14 x) {return x.left;}
static INLINE struct pair14 left15(struct pair15 x) {return x.left;}
static INLINE struct pair15 left16(struct pair16 x) {return x.left;}
static INLINE struct pair16 left17(struct pair17 x) {return x.left;}
static INLINE struct pair17 left18(struct pair18 x) {return x.left;}
static INLINE struct pair18 left19(struct pair19 x) {return x.left;}

static INLINE double right0(struct pair0 x) {return x.right;}
static INLINE struct pair0 right1(struct pair1 x) {return x.right;}
static INLINE struct pair1 right2(struct pair2 x) {return x.right;}
static INLINE struct pair2 right3(struct pair3 x) {return x.right;}
static INLINE struct pair3 right4(struct pair4 x) {return x.right;}
static INLINE struct pair4 right5(struct pair5 x) {return x.right;}
static INLINE struct pair5 right6(struct pair6 x) {return x.right;}
static INLINE struct pair6 right7(struct pair7 x) {return x.right;}
static INLINE struct pair7 right8(struct pair8 x) {return x.right;}
static INLINE struct pair8 right9(struct pair9 x) {return x.right;}
static INLINE struct pair9 right10(struct pair10 x) {return x.right;}
static INLINE struct pair10 right11(struct pair11 x) {return x.right;}
static INLINE struct pair11 right12(struct pair12 x) {return x.right;}
static INLINE struct pair12 right13(struct pair13 x) {return x.right;}
static INLINE struct pair13 right14(struct pair14 x) {return x.right;}
static INLINE struct pair14 right15(struct pair15 x) {return x.right;}
static INLINE struct pair15 right16(struct pair16 x) {return x.right;}
static INLINE struct pair16 right17(struct pair17 x) {return x.right;}
static INLINE struct pair17 right18(struct pair18 x) {return x.right;}
static INLINE struct pair18 right19(struct pair19 x) {return x.right;}

static INLINE double sum(struct pair11 x) {
  return (left0(left1(left2(left3(left4(left5(left6(left7(left8(left9(left10(left11(x))))))))))))+
	  right0(right1(right2(right3(right4(right5(right6(right7(right8(right9(right10(right11(x)))))))))))));}


static double read_real(void) {
  double result;
  scanf("%lf",&result);
  return result;}

int main(void) {
  printf("%f\n", sum(swap11(tree11(tree10(tree9(tree8(tree7(tree6(tree5(tree4(tree3(tree2(tree1(tree0(read_real())))))))))))))));}
