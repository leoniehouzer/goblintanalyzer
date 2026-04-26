// SKIP PARAM: --set ana.activated[+] sparseOctagons --enable ana.int.interval --set 'pre.cppflags[+]' '-std=c99' --trace join --trace leq --trace ops --html
#include <goblint.h>

int main() {
    int one = 1;
    int two = 2;
    int x = 3;

    __goblint_check(one == 1); // SUCCESS
    __goblint_check(two == 2); // SUCCESS
    __goblint_check(x==3); // SUCCESS

    x = f2(one,two);

}

int f2(int a, int b) {

    __goblint_check(a == 1); // SUCCESS
    __goblint_check(b == 2); // SUCCESS

    return 48;
}