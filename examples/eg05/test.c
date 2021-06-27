#include <stdio.h>

int F0() { return 0; }
int F1() { return 1; }
int F2() { return 2; }
int F3() { return 3; }
int F4() { return 4; }


int main()
{
  int (*fp)();
  int (*arr[5])() = { F0, F1, F2, F3, F4 };
  int xyz, i;

  fp = F1;
  xyz = fp();
  printf("The Value is %d\n", xyz);

  for (i = 0; i < 5; i++)
	arr[i]();
  
  printf("\n");
  arr[0]();
  arr[1]();
  arr[2]();
  arr[3]();
  return 0;
}

/* result
int F0(){ return 0; }
int F1(){ return 1; }
int F2(){ return 2; }
int F3(){ return 3; }
int F4(){ return 4; }

int main(){
  int (*fp) () ;
  int (*arr[5])() = {F0, F1, F2, F3, F4};
  int xyz , i ;
  fp = F1;
  xyz = F1();
  printf("The Value is %d\n", xyz);
  for (i = 0; i < 5; i++)
    arr[i] == F0 ? F0() : arr[i] == F1 ? F1() : arr[i] == F2 ? F2() : arr[i] == F3 ? F3() : F4();

  printf("\n");
  arr[0] == F0 ? F0() : arr[0] == F1 ? F1() : arr[0] == F2 ? F2() : arr[0] == F3 ? F3() : F4();
  arr[1] == F0 ? F0() : arr[1] == F1 ? F1() : arr[1] == F2 ? F2() : arr[1] == F3 ? F3() : F4();
  arr[2] == F0 ? F0() : arr[2] == F1 ? F1() : arr[2] == F2 ? F2() : arr[2] == F3 ? F3() : F4();
  arr[3] == F0 ? F0() : arr[3] == F1 ? F1() : arr[3] == F2 ? F2() : arr[3] == F3 ? F3() : F4();
  return 0;
}
*/
