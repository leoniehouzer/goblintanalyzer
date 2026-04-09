// SKIP PARAM: --set ana.activated[+] sparseOctagons --enable ana.int.interval --set 'pre.cppflags[+]' '-std=c99' --trace join --trace leq --trace ops
#include <goblint.h>

int main() {
  int x = 0;
  int y = 1;

  int a = 1 + 2 + 3;
  __goblint_check(a == 6); // SUCCESS

  x = x + 1; 
  y = x + 1; 

  __goblint_check(y == 2); // SUCCESS

  return 0;
}