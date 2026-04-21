// SKIP PARAM: --set ana.activated[+] sparseOctagons --enable ana.int.interval --set 'pre.cppflags[+]' '-std=c99' --trace join --trace leq --trace ops -v
// Example from https://www-apr.lip6.fr/~mine/publi/article-mine-HOSC06.pdf
#include <goblint.h>

int main() {
  int x;
  int unknown;

  if (unknown) {
    x = -5;
  } else {
    x = -7;
  }

  // The above code branches on an uninitialized variable.
  // The value of x could be either -5 or -7.

  // assert(x < 0); // TODO: Thus, this assertion should hold! // funktioniert nicht

  return 0;
}