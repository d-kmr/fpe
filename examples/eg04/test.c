#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct myString {
  char *c;
  int (*length)(struct myString *self);
} myString;

int length(myString *self) {
  return strlen(self->c);
}

myString *init(int n) {
  myString *str = malloc(sizeof(myString));

  str->c = malloc(sizeof(char) * n);
  str->length = length;

  str->c[0] = '\0';

  return str;
}

int main() {
  myString *p = init(30);
  strcpy(p->c, "Hello");
  printf("%d\n", p->length(p)); // function pointer call
  return 0;
}


/* result
typedef struct myString { 
  char *c;
  int  (*length) (struct myString *self);
} myString;

struct myString {
  char *c;
  int  (*length) (struct myString* self);
};

typedef struct myString myString;
int length (myString *self) return strlen(self->c);

myString* init (int n) {
  myString* str = malloc(sizeof(myString));
  str->c = malloc(sizeof (char) * n);
  str->length = length;
  str->c[0] = '\000';
  return str;
}

int main () {
  myString* p = init(30);
  strcpy(p->c, "Hello");
  printf("%d\n", length(p));
  return 0;
}
*/
