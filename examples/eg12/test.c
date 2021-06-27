#include <stdio.h>

typedef enum { Init,Incl,Last,End } Mode;

typedef struct { Mode mode; int value; } State;
                                                                                                    
typedef void (*FP)(State*);                                                                  
                                                                                                    
void init(State* s){
  printf("Init Value: %d\n",s->value);
  s->mode = Incl;
  return;
}

void incl(State* s) {
  s->value++;
  printf("Value: %d\n",s->value);
  if (s->value == 30) s->mode = Last;
  return;
}

void last (State* s) {  
  printf("Last Value: %d\n",s->value);
  s->mode = End;
  return;
}

void end (State* s){
  return;
}

int main() {
  FP fp[] = { init, incl, last, end };
  State s = { Init, 0 };

  for(int i = 0; i < 4 ;i++) fp[i](&s);

  return 0;
}


/* result
typedef enum { Init, Incl, Last, End } Mode;
enum enum_test_c#_1 { Init, Incl, Last,	End};

typedef struct { Mode mode; int value; } State;

struct struct_test_c#_2 { Mode mode; int value; };
typedef struct struct_test_c#_2 State;
typedef void (*FP)(State*);

void init (State* s) {
  printf("Init Value: %d\n", s-> value);
  s-> mode = Incl;
  return;
}

void incl (State* s) {
  s-> value++;
  printf("Value: %d\n", s-> value);
  if (s-> value == 30)
    s-> mode = Last;
  else
    ;
  return;
}

void last (State* s) {
  printf("Last Value: %d\n", s-> value);
  s-> mode = End;
  return;
}

void end (State* s)  return;

int main () {
  FP fp[] = {init, incl, last, end};
  State  s  = {Init, 0};
  for (int i = 0; i < 4; i++)
    fp[i] == init ? init(&s) : fp[i] == incl ? incl(&s) : fp[i] == last ? last(&s) : end(&s);

  return 0;
}
