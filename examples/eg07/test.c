#include <stdio.h>

typedef int (*FP)();
typedef FP (*FunFP)(); // function pointer type that returns FP

static int i=1;

FP funFP(){ // funFP itself has FunFP type
  printf("%d-th call of funFP\n", i++);

  if(i==5)
    return NULL;
  else
    return (FP)funFP;
}

int main(){
  FunFP state = funFP;

  while (state != NULL)
    state = (FunFP)(*state)();

  return 0;
}

/*
typedef int (*FP)();
typedef FP (*FunFP)();

static int i = 1;

FP funFP (){
  printf("%d-th call of funFP\n", i++);
  if (i == 5)
    return NULL;
  else
    return (FP)funFP;
}

int main(){
  FunFP state = funFP;
  while (state != NULL)
    state = (FunFP) funFP();

  return 0;
}
*/
