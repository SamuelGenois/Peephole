/*
 * JOOS is Copyright (C) 1997 Laurie Hendren & Michael I. Schwartzbach
 *
 * Reproduction of all or part of this software is permitted for
 * educational or research use on condition that this copyright notice is
 * included in any copy. This software comes with no warranty of any
 * kind. In no event will the authors be liable for any damages resulting from
 * use of this software.
 *
 * email: hendren@cs.mcgill.ca, mis@brics.dk
 */

/* iload x        iload x        iload x
 * ldc 0          ldc 1          ldc 2
 * imul           imul           imul
 * ------>        ------>        ------>
 * ldc 0          iload x        iload x
 *                               dup
 *                               iadd
 */

int simplify_multiplication_right(CODE **c)
{ int x,k;
  if (is_iload(*c,&x) && 
      is_ldc_int(next(*c),&k) && 
      is_imul(next(next(*c)))) {
     if (k==0) return replace(c,3,makeCODEldc_int(0,NULL));
     else if (k==1) return replace(c,3,makeCODEiload(x,NULL));
     else if (k==2) return replace(c,3,makeCODEiload(x,
                                       makeCODEdup(
                                       makeCODEiadd(NULL))));
     return 0;
  }
  return 0;
}

/* dup
 * astore x
 * pop
 * -------->
 * astore x
 */
int simplify_astore(CODE **c)
{ int x;
  if (is_dup(*c) &&
      is_astore(next(*c),&x) &&
      is_pop(next(next(*c)))) {
     return replace(c,3,makeCODEastore(x,NULL));
  }
  return 0;
}

/* iload x
 * ldc k   (0<=k<=127)
 * iadd
 * istore x
 * --------->
 * iinc x k
 */ 
int positive_increment(CODE **c)
{ int x,y,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_iadd(next(next(*c))) &&
      is_istore(next(next(next(*c))),&y) &&
      x==y && 0<=k && k<=127) {
     return replace(c,4,makeCODEiinc(x,k,NULL));
  }
  return 0;
}

/* goto L1
 * ...
 * L1:
 * goto L2
 * ...
 * L2:
 * --------->
 * goto L2
 * ...
 * L1:    (reference count reduced by 1)
 * goto L2
 * ...
 * L2:    (reference count increased by 1)  
 */
int simplify_goto_goto(CODE **c)
{ int l1,l2;
  if (is_goto(*c,&l1) && is_goto(next(destination(l1)),&l2) && l1>l2) {
     droplabel(l1);
     copylabel(l2);
     return replace(c,1,makeCODEgoto(l2,NULL));
  }
  return 0;
}

/* istore x
 * iload x
 * ----->
 * (removed both)
 * Keep the element in stack for next usage.
*/
int remove_storeloadcouple(CODE **c){
  int x1, x2;
  if(is_istore(*c, &x1) && is_iload(next(*c),&x2)){
    if(x1 == x2){
      return replace(c,2, NULL);
    }
  }
  return 0;
}
/*
 * ldc a
 * iadd
 * ldc b
 * iadd
 * ....
 * ldc n
 * iadd
 * -------->
 * ldc_int (a+b+...+n)
 * iadd
 */
 int add_constants(CODE **c){
   int inc = 0;
   int i;
   int loop = 0;
   CODE *p = *c;
   while(is_ldc_int(p, &i) && is_iadd(next(p))){
     ++loop;
     inc += i;
     p = next(next(p));
   }
   if(loop == 0) return 0;
   return replace(c,loop*2,makeCODEldc_int(inc,
                      makeCODEiadd(NULL)
   ));
 }

/*
 * ldc a
 * imul
 * ldc b
 * imul
 * ....
 * ldc n
 * imul
 * -------->
 * ldc_int (a+b+...+n)
 * imul
 */
 int mul_constants(CODE **c){
   int inc = 0;
   int i;
   int loop = 0;
   CODE *p = *c;
   while(is_ldc_int(p, &i) && is_imul(next(p))){
     inc *= i;
     p = next(next(p));
   }
   if(loop == 0) return 0;

   return replace(c,loop*2,makeCODEldc_int(inc,
                      makeCODEimul(NULL)
   ));
 }
void init_patterns(void) {
	ADD_PATTERN(simplify_multiplication_right);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);
	ADD_PATTERN(remove_storeloadcouple);
	ADD_PATTERN(add_constants);
	ADD_PATTERN(mul_constants);

}
