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

/* ldc x          ldc x
 * iload k        iload k    
 * imul           iadd   
 * ------>        ------>
 * iload k        iload k 
 * ldc x          ldc x
 * imul           iadd
 */
int commutativity(CODE **c) {
  int x,k;
  if (is_ldc_int(*c,&x)
      && is_iload(next(*c),&k)
      && is_imul(next(next(*c)))) {
    return replace(c,2, makeCODEiload(k,
                        makeCODEldc_int(x,
                        makeCODEimul(NULL))));
  }
  else if(is_ldc_int(*c,&x)
          && is_iload(next(*c),&k)
          && is_iadd(next(next(*c)))) {
    return replace(c,2, makeCODEiload(k,
                        makeCODEldc_int(x,
                        makeCODEiadd(NULL))));
  }
  else
    return 0;
}

/* ldc -1         ldc 1  
 * imul           imul   
 * ------>        ------>
 * ineg            
 */
int more_multiplication_simplification(CODE **c) {
  int x;
  if (is_ldc_int(*c,&x) && is_imul(next(*c))) {
     if (x==-1) return replace(c,2,makeCODEineg(NULL));
     else if (x==1) return replace(c,2,NULL);
     return 0;
  }
  return 0;
}

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
/*
 * dup
 * ....A
 * pop
 * ------>
 * ....A
 * A must not affect or use any element that is currently being dup or lower
 * The whole dup -- pop must not contains any label, goto, return or comparison
 * The whole dup -- pop must not change the stack size
 */
int simplify_dup_pop(CODE **c){
  int t_inc = 0, inc, affected, use;
  CODE *p = *c;
  if(is_dup(p)){
    stack_effect(p,&t_inc,&affected,&use);
    p = p->next;
    while(!is_pop(p)){
      if(stack_effect(p,&inc,&affected,&use) == 0 && (t_inc - affected) >= 0 && (t_inc - use) >= 0 && (t_inc += inc) >= 1){
        printf("Something %d\n", t_inc);
        p = p->next;
      }
      else{
        printf("Somethingelse\n");
        return 0;
      }
    }
    printf("t_inc: %d\n",t_inc);
    if(t_inc == 1){
      return replace(c,1,NULL) && replace(&p,1,NULL);
    }
  }
  return 0;
}

 int mul_constants(CODE **c){
   int inc = 0;
   int i;
   int loop = -1;
   CODE *p = *c;
   while(is_ldc_int(p, &i) && is_imul(next(p))){
     ++loop;
     inc *= i;
     p = next(next(p));
   }
   if(loop == 0) return 0;

   return replace(c,(loop+1)*2,makeCODEldc_int(inc,
                      makeCODEimul(NULL)
   ));
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

/* iload x
 * ldc k   (0<=k<=127)
 * isub
 * istore x
 * --------->
 * iinc x -k
 */ 
int negative_increment(CODE **c)
{ int x,y,k;
  if (is_iload(*c,&x) &&
      is_ldc_int(next(*c),&k) &&
      is_isub(next(next(*c))) &&
      is_istore(next(next(next(*c))),&y) &&
      x==y && 0<=k && k<=127) {
     return replace(c,4,makeCODEiinc(x,-k,NULL));
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
 * ldc (a+b+...+n)
 * iadd
 */
 int add_constants(CODE **c){
   int inc = 0;
   int i;
   int loop = -1;
   CODE *p = *c;
   while(is_ldc_int(p, &i) && is_iadd(next(p))){
     ++loop;
     inc += i;
     p = next(next(p));
   }
   if(loop <= 0) return 0;
   return replace(c,(loop+1)*2,makeCODEldc_int(inc,
                      makeCODEiadd(NULL)
   ));
 }

/* dup
 * istore x
 * pop
 * -------->
 * istore x
 */
 
int simplify_istore(CODE **c)
{ int x;
  if (is_dup(*c) &&
      is_istore(next(*c),&x) &&
      is_pop(next(next(*c)))) {
     return replace(c,3,makeCODEistore(x,NULL));
  }
  return 0;
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
 * ldc_int (a*b*...*n)
 * imul
 *
 int mul_constants(CODE **c){
   int inc = 0;
   int i;
   int loop = -1;
   CODE *p = *c;
   while(is_ldc_int(p, &i) && is_imul(next(p))){
     ++loop;
     inc *= i;
     p = next(next(p));
   }
   if(loop == 0) return 0;

   return replace(c,(loop+1)*2,makeCODEldc_int(inc,
                      makeCODEimul(NULL)
   ));
 }
*/

void init_patterns(void) {
	ADD_PATTERN(simplify_multiplication_right);
  ADD_PATTERN(simplify_istore);
	ADD_PATTERN(simplify_astore);
  ADD_PATTERN(simplify_dup_pop);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(negative_increment);
	ADD_PATTERN(simplify_goto_goto);
  ADD_PATTERN(more_multiplication_simplification);
	ADD_PATTERN(add_constants);
/*
	ADD_PATTERN(simplify_multiplication_right);
  ADD_PATTERN(simplify_istore);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);
	ADD_PATTERN(remove_storeloadcouple);
	ADD_PATTERN(add_constants);
	ADD_PATTERN(mul_constants);
  */

}
