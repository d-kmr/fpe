#include <stdio.h>

typedef int (*FP)(int);

int f1(int x){ printf("Called f1: "); return x+2; }

int f2(int x){
  printf("Called f2: ");
  FP fp2 = NULL;
  return fp2(1);
} // never called

int f3(int x){
  printf("Called f3: ");  
  return x+4;
}

int main() {
  FP fp[] = { f1, f2, f3 };
  int i = 0;

  while (i < 100) {
	i = fp[i % 3](i);
	printf("%d\n",i);
  }

  return 0;
}

/* result: Fail (no output)
[reason]
fp2 of the function pointer call fp2(1) does not have a value
even if f2 is never called
*/
