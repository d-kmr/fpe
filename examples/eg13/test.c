#include <stdio.h>

typedef int (*FP)(int);

int f1(int x){ printf("Called f1: "); return x+1; }
int f2(int x){ printf("Called f2: "); return x+2; }
int f3(int x){ printf("Called f3: "); return x+3; } // never called

int main(){
  FP fp[] = { f1, f2, f3 };
  
  int i = 0;
  while (i < 100) {
	i = fp[i % 3](i); // 
	printf("%d\n",i);
  }
  return 0;
}


/* result
typedef int (*FP) (int);
int f1 (int x) { printf("Called f1: "); return x + 1; }
int f2 (int x) { printf("Called f2: "); return x + 2; }
int f3 (int x) { printf("Called f3: "); return x + 3; }

int main () {
  FP  fp[]  = {f1, f2, f3};
  int  i  = 0;
  while (i < 100){
    i = fp[i % 3] == f1 ? f1(i) : fp[i % 3] == f2 ? f2(i) : f3(i);
	printf("%d\n", i);
  }
  return 0;
}
*/
