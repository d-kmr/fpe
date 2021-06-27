#include <stdio.h>

int F(int i, int j) {
  return i << j;
}

int main() {
  int (*fp)(int, int);
  int i;
  fp = F;

  i = (*fp)(10, 3);
  printf("%d", i);
  return 0;
}


/* expected output
int F(int i, int j){
  return i << j;
}

int main() {
  int (*fp)(int, int);
  int i;
  fp = F;
  i = F(10, 3);
  printf("%d", i);
  return 0;
}
*/


