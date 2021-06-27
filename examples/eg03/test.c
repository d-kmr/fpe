#include <stdio.h>

void one(void);
void two(void);
void three(void);

int main() {
  void (*fp[])() = { one , two , three };
  int i;

  printf("Input Number [0-2]> ");
  scanf("%d" , &i);
  if ((i < 0) | (i > 2)) return 0;
  (fp[i])();
  return 0;
}

void one() { printf("one\n"); }

void two() { printf("two\n"); }

void three() { printf("three\n"); }


/*
void one(void);
void two(void);
void three(void);

int main() {
  void  (*fp[]) ()  = {one, two, three};
  int  i ;
  printf("Input Number [0-2]> ");
  scanf("%d", & i);
  if ((i < 0) | (i > 2)) return 0;
  fp[i] == one ? one() : fp[i] == two ? two() : three();
  return 0;
}

void one () { printf("one\n"); }

void two (){ printf("two\n"); }

void three (){ printf("three\n"); }

*/
