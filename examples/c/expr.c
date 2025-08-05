int x = 11;

int *foo() { return &x; }

int main() {
  int a = 1;
  int b = 2;

  // complicated pointers
  int *p1 = &a;
  int **p2 = &p1;
  int **p3 = *&*&p2;

  int *p4 = &b;

  int c = (a == 1 && **p3 == 1) || *foo() == 10;
  int *d = c ? p4 : p1;

  int e = (a = 0) || (b = 5);
  int d_is_5 = *d == 5; // *d should be 5 now

  float dd = 5;
  int dd_is_5 = dd == 5;

  int arr[4][5];
  *&arr[2][3] = 6;

  int arr23_is_6 = arr[2][3] == 6;

  return c && d_is_5 && dd_is_5 && arr23_is_6;
}