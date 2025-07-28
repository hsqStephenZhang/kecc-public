int main(){
    int a = 1;
    int *p = &a;
    int s = sizeof((*p+=1));
    return a;
}