int g = 0;

int* foo() {
    g += 10;
    return &g;
}

int main() {
    *&*foo() += 1;

    return g;
}
