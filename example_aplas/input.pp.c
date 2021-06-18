# 1 "input.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 341 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "input.c" 2
typedef int (*FP)();
struct A { int x; FP fp; };
struct B { struct A* toA; };

FP f;

int one(){ return 1; }
int two(){ return 2; }
int three(){ return 3; }

int main(){
  f = two;
  int n = f();

  f = three;
  n = f();

  FP a[2][1] = { {two}, {three} };
  n = a[1][0]();

  struct A sA = { 0, one };
  struct A* pA = &sA;
  n = pA->fp();
  pA->fp = two;
  n = pA->fp();

  struct B sB = { pA };
  struct B* pB = &sB;
  n = pB->toA->fp();
  return 0;
}
