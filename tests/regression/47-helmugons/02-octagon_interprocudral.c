// SKIP PARAM: --set ana.activated[+] sparseOctagons --enable ana.int.interval --set 'pre.cppflags[+]' '-std=c99' --trace join --trace leq --trace ops -v --html
#include <goblint.h>

int __VERIFIER_nondet_int(void) {
    return rand();
}

int main(void) {
    f1();
}

int f1() {
    int one = __VERIFIER_nondet_int();
    int two = __VERIFIER_nondet_int();

    int x = __VERIFIER_nondet_int();

    one = two;

    // __goblint_check(one - two == 0); // geht nicht
    __goblint_check(one == two); // geht schon(??)
    x = f2(one,two);
    // __goblint_check(one - two == 0);
    __goblint_check(one == two);
    //__goblint_check(x == 48);
}

int f2(int a, int b) {
    // __goblint_check(a-b == 0);
    __goblint_check(a == b);

    return 48;
}
