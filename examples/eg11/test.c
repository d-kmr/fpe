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
  
  while (fp[s.mode] != end)
	fp[s.mode](&s);  
  
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
  while (fp[s. mode] != end)
    fp[s. mode] == init ? init(& s) : fp[s. mode] == incl ? incl(& s) : fp[s. mode] == last ? last(& s) : end(& s);

  return 0;
}
*/
