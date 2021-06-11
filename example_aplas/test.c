#include<stdio.h>
#include<stdlib.h>

typedef void (*FP)();
struct A { int x; FP fp; };
struct B { struct A* toA; };

FP f;

void one(){ printf("1"); return; }
void two(){ printf("2"); return; }
void three(){ printf("3"); return; }

int main(){
  f = two; f();
  f = three; f();
  
  struct A* sA = malloc(sizeof(struct A));
  sA->x = 0;
  sA->fp = one; sA->fp();
  sA->fp = two; sA->fp();
  
  struct B* sB = malloc(sizeof(struct B));
  sB->toA = sA;
  sB->toA->fp();

  int x = 0;
  
  FP a[2][1] = { {two}, {three} };
  a[1][0]();

  return 0;
}
// --------------
