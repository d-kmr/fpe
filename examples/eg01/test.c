#include <stdio.h>

void F() {
  printf("Hello World.\n");
}

int main() {
  void (*fp)() = F;
  fp();
  return 0;
}

/* expected output
void  F (){ printf("Hello World.\n"); }

int  main () {
  void  (*fp)() = F;
  F();
  return 0;
}
*/
