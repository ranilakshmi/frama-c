/*@
    ensures \result >=0;
    ensures (\result==n) || (\result == -n);
*/
int abs(int n){
    if(n<0){
        return -n;
    }
    return n;
}
