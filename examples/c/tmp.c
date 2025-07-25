struct Inner{
    int a;
    int b;
};

struct color {
    int number;
    char name;
    struct Inner inner;
};

int main() {
    // struct color c = {.number = 1, .name = 2, .inner = {.a = 3, .b = 4}};
    struct color c = {1, .name =2, {.a = 3, .b = 4}};
    return 0;
}
