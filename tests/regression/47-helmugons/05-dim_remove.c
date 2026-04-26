// SKIP PARAM: --set ana.activated[+] sparseOctagons --enable ana.int.interval --set 'pre.cppflags[+]' '-std=c99' --trace join --trace leq --trace ops --html
#include <goblint.h>

int main() {
    int one = 1;
    int two = 2;
    int y = 3;
    int x = 4;

    y = f1(); // Problem: return value kommt nicht an. und es kommen ganz komische binarys dazu:
    // - one + y <= 0 und - y + one <= 0 

    __goblint_check(one == 1); // SUCCESS
    __goblint_check(two == 2); // SUCCESS
    __goblint_check(x == 4); // SUCCESS

    // __goblint_check(y != 3); // SUCCESS
    // __goblint_check(y == 3); // FAILURE

    __goblint_check(y == 42); // SUCCESS
    // __goblint_check(y == 42); // SUCCESS

    y = 42;
    x = f2(one,two);

    __goblint_check(one == 1); // SUCCESS
    __goblint_check(two == 2); // SUCCESS
    __goblint_check(y == 42); // SUCCESS

    // __goblint_check(x != 4); // SUCCESS
    // __goblint_check(x == 4); // FAILURE

    // __goblint_check(x == 48); // SUCCESS
    // __goblint_check(x == 48); // SUCCESS

}

int f1() {
    return 42; // return value ist hier richtig, kommt aber nicht in main an.
}

int f2(int a, int b) {
    return 48;
}

