#include <stdio.h>

#define INLINE inline __attribute__ ((always_inline))

struct pair0 {double left;double right;};
struct pair1 {struct pair0 left;struct pair0 right;};
struct pair2 {struct pair1 left;struct pair1 right;};
struct pair3 {struct pair2 left;struct pair2 right;};
struct pair4 {struct pair3 left;struct pair3 right;};

static INLINE struct pair0 tree0(double x);
static INLINE struct pair1 tree1(struct pair0 x);
static INLINE struct pair2 tree2(struct pair1 x);
static INLINE struct pair3 tree3(struct pair2 x);
static INLINE struct pair4 tree4(struct pair3 x);
static INLINE struct pair0 swap0(struct pair0 x);
static INLINE struct pair1 swap1(struct pair1 x);
static INLINE struct pair2 swap2(struct pair2 x);
static INLINE struct pair3 swap3(struct pair3 x);
static INLINE struct pair4 swap4(struct pair4 x);
static INLINE double left0(struct pair0 x);
static INLINE struct pair0 left1(struct pair1 x);
static INLINE struct pair1 left2(struct pair2 x);
static INLINE struct pair2 left3(struct pair3 x);
static INLINE struct pair3 left4(struct pair4 x);
static INLINE double right0(struct pair0 x);
static INLINE struct pair0 right1(struct pair1 x);
static INLINE struct pair1 right2(struct pair2 x);
static INLINE struct pair2 right3(struct pair3 x);
static INLINE struct pair3 right4(struct pair4 x);
static INLINE double sum(struct pair4 x);
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

static INLINE double left0(struct pair0 x) {return x.left;}
static INLINE struct pair0 left1(struct pair1 x) {return x.left;}
static INLINE struct pair1 left2(struct pair2 x) {return x.left;}
static INLINE struct pair2 left3(struct pair3 x) {return x.left;}
static INLINE struct pair3 left4(struct pair4 x) {return x.left;}

static INLINE double right0(struct pair0 x) {return x.right;}
static INLINE struct pair0 right1(struct pair1 x) {return x.right;}
static INLINE struct pair1 right2(struct pair2 x) {return x.right;}
static INLINE struct pair2 right3(struct pair3 x) {return x.right;}
static INLINE struct pair3 right4(struct pair4 x) {return x.right;}

static INLINE double sum(struct pair4 x) {
  return (left0(left1(left2(left3(left4(x)))))+
	  right0(right1(right2(right3(right4(x))))));}

static double read_real(void) {
  double result;
  scanf("%lf",&result);
  return result;}

int main(void) {
  printf("%f\n", sum(swap4(tree4(tree3(tree2(tree1(tree0(read_real()))))))));}
