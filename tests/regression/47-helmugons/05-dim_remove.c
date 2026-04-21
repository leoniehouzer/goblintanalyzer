// SKIP PARAM: --set ana.activated[+] sparseOctagons --enable ana.int.interval --set 'pre.cppflags[+]' '-std=c99' --trace join --trace leq --trace ops --html
#include <goblint.h>

int main() {
    int one = 1;
    int two = 2;
    int y = 3;
    int x = 4;

    y = f1(); // Problem: return value kommt nicht an.

    assert(one == 1); // SUCCESS
    assert(two == 2); // SUCCESS
    assert(x == 4); // SUCCESS

    // assert(y != 3); // SUCCESS
    // assert(y == 3); // FAILURE

    // assert(y == 42); // SUCCESS
    // __goblint_check(y == 42); // SUCCESS

    y = 42;
    x = f2(one,two);

    assert(one == 1); // SUCCESS
    assert(two == 2); // SUCCESS
    assert(y == 42); // SUCCESS

    // assert(x != 4); // SUCCESS
    // assert(x == 4); // FAILURE

    // assert(x == 48); // SUCCESS
    // __goblint_check(x == 48); // SUCCESS

}

int f1() {

    return 42; // return value ist hier richtig, kommt aber nicht in main an.

}

int f2(int a, int b) {

    return 48;

}

