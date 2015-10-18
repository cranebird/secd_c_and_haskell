#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <printf.h>

#define fxnum_shift 2
#define fxnum_mask 0b11
#define fxnum_tag 0b00
#define immediate_true 0b10011111
#define immediate_false 0b00011111
#define cons_mask 0b111
#define cons_tag 0b001
#define immediate_nil 0b01001111
// INSN
#define NIL  0b0000100000111
#define LD   0b0001000000111
#define LDC  0b0001100000111
#define SEL  0b0010000000111
#define JOIN 0b0010100000111
#define ATOM 0b0011000000111
#define LDF  0b0011100000111
#define CONS 0b0100000000111
#define AP   0b0100100000111
#define RTN  0b0101000000111
#define DUM  0b0101100000111
#define RAP  0b0110000000111
#define ADD  0b0110100000111
#define SUB  0b0111000000111
#define MUL  0b0111100000111
#define LTN  0b1000000000111
#define GTN  0b1000100000111
// Omega
#define Omega  0b11110111

typedef intptr_t obj;

void show_object (intptr_t x);
void show_cons (intptr_t x);
void print_bin(intptr_t x);
intptr_t cons (intptr_t x, intptr_t y);
void show_cons_iter1 (intptr_t x, intptr_t y);
void show_cons_iter2 (intptr_t x);
intptr_t car (intptr_t x);
intptr_t cdr (intptr_t x);
void evalVM1();
void eval();
void show_secd();
void rplaca (intptr_t x, intptr_t v);
intptr_t nth (intptr_t i, intptr_t p);

// SECD Registers
intptr_t s;
intptr_t e;
intptr_t c;
intptr_t d;
intptr_t fp;
int ncons = 0;

void show_object (intptr_t x) {
  if ((x & fxnum_mask) == fxnum_tag) {
    printf("%lu", x >> fxnum_shift);
  } else if (x == immediate_true) {
    printf("#t");
  } else if (x == immediate_false) {
    printf("#f");
  } else if ((x & cons_mask) == cons_tag) {
    printf("(");
    show_cons(x);
  } else if (x == immediate_nil) {
    printf("()");
  } else if (x == NIL) {
    printf("NIL");
  } else if (x == LD) {
    printf("LD");
  } else if (x == LDC) {
    printf("LDC");
  } else if (x == SEL) {
    printf("SEL");
  } else if (x == JOIN) {
    printf("JOIN");
  } else if (x == ATOM) {
    printf("ATOM");
  } else if (x == LDF) {
    printf("LDF");
  } else if (x == CONS) {
    printf("CONS");
  } else if (x == AP) {
    printf("AP");
  } else if (x == RTN) {
    printf("RTN");
  } else if (x == DUM) {
    printf("DUM");
  } else if (x == RAP) {
    printf("RAP");
  } else if (x == ADD) {
    printf("ADD");
  } else if (x == SUB) {
    printf("SUB");
  } else if (x == MUL) {
    printf("MUL");
  } else if (x == LTN) {
    printf("LTN");
  } else if (x == GTN) {
    printf("GTN");
  } else if (x == Omega) {
    printf("Omega");
  } else {
    printf ("#<unkown %lu>", x);
  }
}

void show_cons (intptr_t x) {
  intptr_t fst = car (x);
  intptr_t rest = cdr (x);
  show_cons_iter1 (fst, rest);
}

void show_cons_iter1 (intptr_t x, intptr_t y) {
  show_object (x);
  show_cons_iter2 (y);
}

void show_cons_iter2 (intptr_t x) {
  if (x == immediate_nil) {
    printf(")");
  } else if ((x & cons_mask) == cons_tag) {
    printf(" ");
    intptr_t fst = car (x);
    intptr_t rest = cdr (x);
    show_cons_iter1 (fst, rest);
  } else {
    printf(" . ");
    show_object (x);
    printf(")");
  }
}
// 二進出力
void print_bin(intptr_t x) {
  int i;
  for (i = 64 -1; i>= 0; i --) {
    printf("%ld", (x >> i) & 1);
  }
  printf("\n");
}

intptr_t cons (intptr_t x, intptr_t y) {
  int* fpptr = (int *) malloc (2);
  fp = (intptr_t) fpptr;

  intptr_t fp0 = fp;
  int* p = (int*) fp;
  *p = x;
  *(p + 2) = y;
  
  fp = fp + 8 * (2 * 8);
  fp0 = fp0 | 0x01; // タグを付与して返却
  ncons++;
  return fp0;
}

intptr_t car (intptr_t x) {
  int* p = (int*)(x ^ 0x001);
  return (intptr_t)*p;
}

intptr_t cdr (intptr_t x) {
  int* p = (int*)(x ^ 0x001);
  return (intptr_t)*(p + 2);
}

intptr_t caar (intptr_t x) {
  return car (car (x));
}
intptr_t cadr (intptr_t x) {
  return car (cdr (x));
}
intptr_t cdar (intptr_t x) {
  return cdr (car (x));
}
intptr_t cddr (intptr_t x) {
  return cdr (cdr (x));
}

intptr_t locate (intptr_t ij, intptr_t e) {
  intptr_t i = car (ij);
  intptr_t j = cdr (ij);
  intptr_t ii = i >> fxnum_shift;
  intptr_t jj = j >> fxnum_shift;
  return nth (jj -1, nth (ii - 1, e));
}

void eval() {
  while(true) {
    if (c == immediate_nil) {
      break;
    }
    // show_secd();
    evalVM1();
  }
}

intptr_t nth (intptr_t i, intptr_t p) {
  if (i == 0) {
    return car (p);
  } else {
    intptr_t p1 = cdr (p);
    return nth (i -1, p1);
  }
}

void evalVM1() {
  intptr_t op = car (c);
  switch (op) {
  case NIL: // s e (NIL.c) d        ->  (nil.s) e c d
    {
      s = cons (immediate_nil, s);
      c = cdr (c);
      break;
    }
  case LD: // s e (LD (i.j).c) d   ->  (locate((i.j),e).s) e c d
    {
      s = cons (locate (cadr (c), e), s);
      c = cddr (c);    
      break;
    }
  case LDC: // s e (LDC x.c) d -> (x.s) e c d  
    {
      s = cons (cadr (c), s);
      c = cddr (c);
      break;
    }
  case LDF: // s e (LDF f.c) d ->  ((f.e).s) e c d  
    {
      s = cons (cons (cadr (c), e), s);
      c = cddr (c);
      break;
    }
  case CONS: // (a b.s') e (OP.c) d   ->   ((a.b).s') e c d
    {
      s = cons (cons (car (s), cadr (s)), cddr (s));
      c = cdr (c);
      break;
    }
  case AP: // ((f.e') v.s') e (AP.c') d    ->  NIL (v.e') f (s' e c'.d)  
    {
      intptr_t f = caar (s);
      intptr_t e1 = cdar (s);
      intptr_t v = cadr (s);
      intptr_t s1 = cddr (s);
      intptr_t e0 = e; // 順番重要
      intptr_t c1 = cdr (c);
      intptr_t e2 = cons (v, e1);

      s = immediate_nil;
      e = e2;
      c = f;
      d = cons (s1, (cons (e0, (cons (c1, d)))));
      break;
    }
  case RTN: // (x.z) e' (RTN.q) (s1 e1 c1.d1) ->  (x.s1) e1 c1 d1
    {
      s = cons (car (s), car (d));
      e = cadr (d);
      c = car (cddr (d));
      d = cdr (cddr (d));
      break;
    }
  case ADD: // (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    {
      intptr_t x = car (s) + cadr (s); // タグは無視して足せる
      s = cons (x, (cddr (s)));
      c = cdr (c);
      break;
    }
  case SUB: // (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    {
      intptr_t x = car (s) - cadr (s); // タグは無視して引ける
      s = cons (x, (cddr (s)));
      c = cdr (c);
      break;
    }
  case MUL: // (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    {
      intptr_t a = car (s);
      intptr_t b = cadr (s);
      intptr_t x = (a >> fxnum_shift) * b;
      s = cons (x, (cddr (s)));
      c = cdr (c);
      break;
    }
  case GTN: // (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    {
      intptr_t x = car (s) > cadr (s) ? immediate_true : immediate_nil;
      s = cons (x, (cddr (s)));
      c = cdr (c);
      break;
    }
  case LTN: // (a b.s) e (OP.c) d   ->   ((a OP b).s) e c d
    {
      intptr_t x = car (s) < cadr (s) ? immediate_true : immediate_nil;
      s = cons (x, (cddr (s)));
      c = cdr (c);
      break;
    }
  case SEL: // (x.s) e (SEL ct cf .c') d -> s e cx (c'.d) where cx = ct if x = #t
    {
      intptr_t x = car (s);
      intptr_t ct = cadr (c);
      intptr_t cf = car (cddr (c));
      s = cdr (s);
      d = cons (cdr (cdr (cdr (c))), d);
      if (x == immediate_true) {
	c = ct;
      } else {
	c = cf;
      }
      break;
    }
 case JOIN: // s e (JOIN.c) (cr.d)  ->  s e cr d
   {
     intptr_t cr = car (d);
     c = cr;
     d = cdr (d);
     break;
   }
  case ATOM:
    {
      intptr_t x = car (s);
      if ((x & cons_mask) == cons_tag) {
	s = cons (immediate_false, cdr (s));
      } else {
	s = cons (immediate_true, cdr (s));
      }
      c = cdr (c);
      break;
    }
  case DUM: // s e (DUM.c) d  ->  s (W.e) c d
    {
      e = cons (Omega, e);
      c = cdr (c);
      break;
    }
  case RAP: // ((f.(W.e)) v.s') (W.e) (RAP.c) d ->  nil rplaca((W.e),v) f (s' e c.d)
    {
      intptr_t f = caar (s);
      intptr_t we = cdar (s);
      intptr_t v = cadr (s);
      intptr_t s1 = cddr (s);
      intptr_t c1 = cdr (c);
      intptr_t e1 = cdr (e);
      rplaca (we, v);
      s = immediate_nil;
      e = we;
      c = f;
      d = cons (s1, cons (e1, cons (c1, d)));
      break;
    }
  default:
    printf("unkown op: %ld\n", op);
    exit (1);
  }
}

void rplaca (intptr_t x, intptr_t v) {
  int* p = (int*)(x ^ 0x001);
  *p = v;
}

void show_secd () {
  show_object (s);
  printf(" ");
  show_object (e);
  printf(" ");
  show_object (c);
  printf(" ");
  show_object (d);
  printf("\n");
  printf("ncons %d\n", ncons);
}


void cons_test () {
  printf("# cons_test\n");
  // (cons 7 9)
  intptr_t x = cons (7 << fxnum_shift, 9 << fxnum_shift);
  printf("x = #0x%08lx ", x);
  show_object(x);
  printf("\n");

  intptr_t p = car (x);
  printf("car: #0x%08lx ", p);
  show_object(p);
  printf("\n");

  intptr_t q = cdr (x);
  printf("cdr: #0x%08lx ", q);
  show_object(q);
  printf("\n");

}

void cons_test_2 () {
  printf("# cons_test_2\n");
  // (cons 65 Nil)
  intptr_t x = cons (65 << fxnum_shift, immediate_nil);
  printf("x = #0x%08lx ", x);
  show_object(x);
  printf("\n");

  intptr_t p = car (x);
  printf("car: #0x%08lx ", p);
  show_object(p);
  printf("\n");

  intptr_t q = cdr (x);
  printf("cdr: #0x%08lx ", q);
  show_object(q);
  printf("\n");
}

void cons_test_3 () {
  //  (7 5 9)
  printf("# cons_test_3\n");
  intptr_t x0 = cons (9 << fxnum_shift, immediate_nil);
  intptr_t x1 = cons (5 << fxnum_shift, x0);
  intptr_t x = cons (7 << fxnum_shift, x1);
  show_object(x);
  printf("\n");

  /* printf("x0: #0x%08lx\n", x0); */
  /* printf("x1: #0x%08lx\n", x1); */
  /* printf("x: #0x%08lx\n", x); */

  intptr_t p = car (x);
  printf("car: #0x%08lx ", p);
  show_object(p);
  printf("\n");

  intptr_t q = cdr (x);
  printf("cdr: #0x%08lx ", q);
  show_object(q);
  printf("\n");

  intptr_t r = car (q);
  printf("cadr: #0x%08lx ", r);
  show_object(r);
  printf("\n");
}

void cons_test_4 () {
  //  (7 5 9)
  printf("# cons_test_4\n");
  intptr_t x = cons (7 << fxnum_shift, (cons (5 << fxnum_shift, cons (9 << fxnum_shift, immediate_nil))));
  show_object(x);
  printf("\n");
}

////////////////////////////////////////////////////////////////
// test
////////////////////////////////////////////////////////////////
void insn_test() {
  intptr_t insns[] = { NIL, LD, LDC, SEL, JOIN,
		       ATOM, LDF, CONS, AP, RTN,
		       DUM, RAP, ADD, SUB, MUL,
		       LTN, GTN };
  int i;
  for (i = 0; i < 16; i++) {
    printf("insn %ld\n", insns[i]);
  }
}

void nil_test() {
  c = cons (NIL, immediate_nil);
  show_object(c);
  evalVM1();
}

void ldc_test() {
  c = cons (LDC, cons (11 << fxnum_shift, immediate_nil));
  show_object(c);
  evalVM1();
}

void ap_test() {
  /*
Example. ((lambda (x y) (+ x y)) 2 3) compiles to
      (NIL LDC 3 CONS LDC 2 CONS LDF (LD (1.2) LD (1.1) + RTN) AP)
*/
  intptr_t a1 = cons (1 << fxnum_shift, 2 << fxnum_shift);
  intptr_t a2 = cons (1 << fxnum_shift, 1 << fxnum_shift);
  intptr_t f = cons (LD, (cons (a1, (cons (LD, (cons (a2, (cons (ADD, (cons (RTN, immediate_nil)))))))))));
  c = cons (NIL, (cons (LDC, (cons (3 << fxnum_shift, (cons (CONS, (cons (LDC, (cons (2 << fxnum_shift, (cons (CONS, (cons (LDF, (cons (f, (cons (AP, immediate_nil)))))))))))))))))));
  eval();
}

void gtn_test() {
  c = cons (LDC, cons (1 << fxnum_shift, (cons (LDC, (cons (9 << fxnum_shift, (cons (GTN, immediate_nil))))))));
  show_secd();
  eval();
}

void sel_test() {
  intptr_t ct = cons (LDC, cons (9 << fxnum_shift, cons (JOIN, immediate_nil)));
  intptr_t cf = cons (LDC, cons (7 << fxnum_shift, cons (JOIN, immediate_nil)));
  c = cons (LDC, cons (5 << fxnum_shift, cons (ATOM, cons (SEL, cons (ct, cons (cf, immediate_nil))))));
  eval();
}

/*
  dum;
  nil;
  ldf (do { 
          ldc 2;
          ld (1,1);
          ltn;
          sel 
          (do { ld (1,1); join_ })
          (do { nil; ldc 2; ld (1,1); sub; cons_;
                ld (2,1); ap_; nil; ldc 1; ld (1,1);
                sub; cons_; ld (2,1); ap_; add; join_});
          rtn; });
  cons_; 
  ldf (do { nil; ldc x; cons_; ld (1,1); ap_; rtn });
  rap; 
*/

/*
(DUM
 NIL
 LDF (LDC 2 LD (1 . 1) LTN SEL (LD (1 . 1) JOIN) (NIL LDC 2 LD (1 . 1) SUB CONS LD (2 . 1) AP NIL LDC 1 LD (1 . 1) SUB CONS LD (2 . 1) AP ADD JOIN) RTN)
 CONS
 LDF (NIL LDC 1 CONS LD (1 . 1) AP RTN) RAP)

*/
void fib_test(int n) {
  intptr_t argbr1_1 = cons (1 << fxnum_shift, 1 << fxnum_shift);
  intptr_t br1 = cons (LD, cons (argbr1_1, cons (JOIN, immediate_nil)));

  intptr_t argbr2_1 =  cons (1 << fxnum_shift, 1 << fxnum_shift); // (1,1)
  intptr_t argbr2_2 =  cons (2 << fxnum_shift, 1 << fxnum_shift); // (2,1)
  intptr_t br2 = cons (NIL, cons (LDC, cons (2 << fxnum_shift, cons (LD, cons (argbr2_1, cons (SUB, cons (CONS, cons (LD, cons (argbr2_2, cons (AP, cons (NIL, cons (LDC, cons (1 << fxnum_shift, cons (LD, cons (argbr2_1, cons (SUB, cons (CONS, cons (LD, cons (argbr2_2, cons (AP, cons (ADD, cons (JOIN, immediate_nil))))))))))))))))))))));

  intptr_t argg_1 = cons (1 << fxnum_shift, 1 << fxnum_shift);
  intptr_t g = cons (NIL, cons (LDC, cons (n << fxnum_shift, cons (CONS, cons (LD, cons (argg_1, (cons (AP, cons (RTN, immediate_nil)))))))));

  intptr_t argf = cons (1 << fxnum_shift, 1 << fxnum_shift);
  intptr_t f = cons (LDC, cons (2 << fxnum_shift, cons (LD, cons (argf, cons (LTN, cons (SEL, cons (br1, cons (br2, cons (RTN, immediate_nil)))))))));
  c = cons (DUM, cons (NIL, cons (LDF, cons (f, cons (CONS, cons (LDF, cons (g, cons (RAP, immediate_nil))))))));
  show_secd();
  eval();
  show_secd(); 
}

int main () {
  /* printf("sizeof int: %ld\n", sizeof (int)); // = 4 */
  /* printf("sizeof int*: %ld\n", sizeof (int*)); // = 8 */
  /* printf("sizeof intptr_t: %ld\n", sizeof (intptr_t)); // 8 == sizeof (int*) */

  int* fpptr = (int *) malloc (100);
  fp = (intptr_t) fpptr;
  printf("fp: 0x%ld\n", fp);
  s = immediate_nil;
  e = immediate_nil;
  c = immediate_nil;
  d = immediate_nil;

  /* cons_test(); */
  /* cons_test_2(); */
  /* cons_test_3(); */
  /* cons_test_4(); */
  /* ldc_test(); */
  /* nil_test(); */
  /* ap_test(); */
  /* gtn_test(); */
  /* sel_test(); */
  fib_test(23);
//  show_secd();
  return 0;
}
