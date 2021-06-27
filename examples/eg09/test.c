#include<stdio.h>
#include<math.h>

double plus (double x, double y){
  return x+y;
}

double applyDup (double (*f)(double,double), double x) {
  return f(x,x);
}

int main () {
  double result = applyDup (plus, 5.0);
  printf("result = %g\n", result);
  
  result = applyDup (pow, 5.0);
  printf("result = %g\n", result);
  
  return 0;
}


/* result
double plus (double x, double y) {
  return x+y;
}

double applyDup (double (*f)(double,double), double x) {
  return f == plus ? plus(x, x) : pow(x, x);
}

int main () {
  double result = applyDup(plus, 5.0);
  printf("result = %g\n", result);
  
  result = applyDup(pow, 5.0);
  printf("result = %g\n", result);
  
  return 0;
}
*/
