typedef int (*FUNC)(int, int);

int sum(int a, int b) { return a+b; }
int sub(int a, int b) { return a-b; }
int mul(int a, int b) { return a*b; }
int div(int a, int b) { return a/b; }

FUNC p[4] = { sum, sub, mul, div };

int main(void){
  int result;
  int i = 2, j = 3, op = 2;

  result = p[op](i, j);
  return 0;
}

/*
typedef int FUNC (int, int);

FUNC p[4] = {sum, sub, mul, div};
int sum(int a,int b){ return a+b; }
int sub(int a,int b){ return a-b; }
int mul(int a,int b){ return a*b; }
int div(int a,int b){ return a/b; }

int main (void){
  int  result ;
  int  i = 2, j = 3, op = 2;
  result = p[op] == sum ? sum(i, j) : p[op] == sub ? sub(i, j) : p[op] == mul ? mul(i, j) : div(i, j);
  return 0;
}
*/
