/*@
    behavior one:
        assumes a>=b;
        ensures \result == a-b;
    behavior two:
        assumes a<b;
        ensures \result == b-a;
    complete behaviors;
    disjoint behaviors;
*/
int distance(int a,int b){
    if (a>b){
        return a-b;
    }
    return b-a;
}
