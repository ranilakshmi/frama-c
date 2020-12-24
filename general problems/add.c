#include<limits.h>
/*@
    requires a+b<INT_MAX;
    ensures \result == a+b;
*/
int add(int a,int b){
    return a+b;
}
