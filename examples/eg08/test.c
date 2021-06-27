#include<stdio.h>
#include<math.h>

double plusOne(double x) {
  return x+1.0;
}

double apply(double (*f)(double), double x) {
  return f(x);
}

int main() {
  double result = apply(plusOne, 5.0);
  printf("result = %g\n", result);
  
  result = apply(sqrt, 5.0);
  printf("result = %g\n", result);
  
  return 0;
}



/* result
double plusOne (double x) {
  return x + 1.0;
}

double apply (double (*f)(double), double x) {
  return f == plusOne ? plusOne(x) : sqrt(x);
}

int main () {
  double  result = apply(plusOne, 5.0);
  printf("result = %g\n", result);
  
  result = apply(sqrt, 5.0);
  printf("result = %g\n", result);
  
  return 0;
}
*/
