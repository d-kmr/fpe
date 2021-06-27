#include <stdio.h>

void sub(long(* pfunc)(int, short), int num){
    return;
}

int main(void){
    long (*pfunc)(int, short) = NULL;
    sub(pfunc, 100);
    return 0;
}

/*
Not changed since pfunc has no value
*/
