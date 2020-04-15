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

/* if_x L1
 * iconst_0
 * goto L2
 * L1:      (is unique)
 * iconst_1
 * L2:      (is unique)
 * ifeq L3
 * ...
 * L3:
 * --------->
 * if_notx L3
 * ...
 * L3:  
 */
int ifsimplify(CODE **c) {
  int val,l1a,l1b,l2a,l2b,l3;
  if( is_if(c, &l1a)
      && is_ldc_int(nextby(*c,1),&val) && val == 0
      && is_goto(nextby(*c,2),&l2a)
      && is_label(nextby(*c,3),&l1b) && l1a == l1b && uniquelabel(l1b)
      && is_ldc_int(nextby(*c,4),&val) && val == 1
      && is_label(nextby(*c,5),&l2b) && l2a == l2b && uniquelabel(l2b)
      && is_ifeq(nextby(*c,6), &l3)
    ) {
    droplabel(l1a);
    droplabel(l2a);
    if(is_ifeq(*c, &l1a))
      return replace(c,7, makeCODEifne(l3,NULL));
    if(is_ifne(*c, &l1a))
      return replace(c,7, makeCODEifeq(l3,NULL));
    if(is_ifnull(*c, &l1a))
      return replace(c,7, makeCODEifnonnull(l3,NULL));
    if(is_ifnonnull(*c, &l1a))
      return replace(c,7, makeCODEifnull(l3,NULL));
    if(is_if_acmpeq(*c, &l1a))
      return replace(c,7, makeCODEif_acmpne(l3,NULL));
    if(is_if_acmpne(*c, &l1a))
      return replace(c,7, makeCODEif_acmpeq(l3,NULL));
    if(is_if_icmpeq(*c, &l1a))
      return replace(c,7, makeCODEif_icmpne(l3,NULL));
    if(is_if_icmpne(*c, &l1a))
      return replace(c,7, makeCODEif_icmpeq(l3,NULL));
    if(is_if_icmpgt(*c, &l1a))
      return replace(c,7, makeCODEif_icmple(l3,NULL));
    if(is_if_icmple(*c, &l1a))
      return replace(c,7, makeCODEif_icmpgt(l3,NULL));
    if(is_if_icmpge(*c, &l1a))
      return replace(c,7, makeCODEif_icmplt(l3,NULL));
    if(is_if_icmplt(*c, &l1a))
      return replace(c,7, makeCODEif_icmpge(l3,NULL));
  }
  return 0;
}

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
    return replace(c,3, makeCODEiload(k,
                        makeCODEldc_int(x,
                        makeCODEimul(NULL))));
  }
  else if(is_ldc_int(*c,&x)
          && is_iload(next(*c),&k)
          && is_iadd(next(next(*c)))) {
    return replace(c,3, makeCODEiload(k,
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
 * This peephole overides simplify_astore peephole.
 */
int simplify_dup_pop(CODE **c){
  int t_inc = 0, inc, affected, use;
  CODE *p = *c;
  if(is_dup(p)){
    stack_effect(p,&t_inc,&affected,&use);
    while(!is_pop(next(p))){
      p = next(p);
      if(stack_effect(p,&inc,&affected,&use) == 0 && (t_inc + affected) >= 0 && (t_inc + use) >= 0 && (t_inc += inc) >= 0){
      }
      else{
        return 0;
      }
    }
    if(t_inc == 0){
      p->next = next(next(p));
      return replace(c,1,NULL);
    }
  }
  return 0;
}

/*
 * aload x (iload x)
 * aload y (iload y)
 * swap
 * -------->
 * aload y (iload y)
 * aload x (iload x)
*/
int simplify_swap(CODE **c){
  int x, y;
  if(is_iload(*c, &x)
   && is_iload(next(*c), &y)
    && is_swap(next(next(*c))
    )){
    return replace(c,3,makeCODEiload(y,
                      makeCODEiload(x,NULL)));
  }
  else if(is_aload(*c, &x)
   && is_iload(next(*c), &y)
    && is_swap(next(next(*c)))
    ){
    return replace(c,3,makeCODEiload(y,
                      makeCODEaload(x,NULL)));
  }
  else if(is_iload(*c, &x)
   && is_aload(next(*c), &y)
    && is_swap(next(next(*c)))
    ){
    return replace(c,3,makeCODEaload(y,
                      makeCODEiload(x,NULL)));
  }
  else if(is_aload(*c, &x)
   && is_aload(next(*c), &y)
    && is_swap(next(next(*c)))
    ){
    return replace(c,3,makeCODEaload(y,
                      makeCODEaload(x,NULL)));
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

/* use_label L1
 * ...
 * use_label L2
 * ...
 * L1:
 * L2:
 * --------->
 * use_label L2
 * ...
 * use_label L2
 * ...
 * L2:    (drop all label that refer to the same instruction)  
 * This is going to be hard because the way labels are stored is inconsistent.
 */
int simplify_same_instruction_label(CODE **c){
  int l1, l2;
  int l_change = 0;
  CODE *p = *c;
  if(uses_label(p,&l1)){
    droplabel(l1);
    p = destination(l1);
    while(is_label(next(p),&l2)){
      l_change = 1;
      l1 = l2;
      p = next(p);
    }
    copylabel(l1);
    if(l_change){
      if(is_goto(*c,&l2))
        return replace(c,1,makeCODEgoto(l1,NULL));
      else if(is_ifeq(*c,&l2))
        return replace(c,1,makeCODEifeq(l1,NULL));
      else if(is_ifne(*c,&l2))
        return replace(c,1,makeCODEifne(l1,NULL));
      else if(is_if_acmpeq(*c,&l2))
        return replace(c,1,makeCODEif_acmpeq(l1,NULL));
      else if(is_if_acmpne(*c,&l2))
        return replace(c,1,makeCODEif_acmpne(l1,NULL));
      else if(is_ifnull(*c,&l2))
        return replace(c,1,makeCODEifnull(l1,NULL));
      else if(is_ifnonnull(*c,&l2))
        return replace(c,1,makeCODEifnonnull(l1,NULL));
      else if(is_if_icmpeq(*c,&l2))
        return replace(c,1,makeCODEif_icmpeq(l1,NULL));
      else if(is_if_icmpgt(*c,&l2))
        return replace(c,1,makeCODEif_icmpgt(l1,NULL));
      else if(is_if_icmplt(*c,&l2))
        return replace(c,1,makeCODEif_icmplt(l1,NULL));
      else if(is_if_icmple(*c,&l2))
        return replace(c,1,makeCODEif_icmple(l1,NULL));
      else if(is_if_icmpge(*c,&l2))
        return replace(c,1,makeCODEif_icmpge(l1,NULL));
      else if(is_if_icmpne(*c,&l2))
        return replace(c,1,makeCODEif_icmpne(l1,NULL));
    }
  }
  else if(is_label(p,&l1) && is_label(next(p),&l2)){
    return replace(c,1,NULL);
  }
  return 0;
}

/* astore x (istore x)
 * aload x  (iload x)
 * ...A
 * return (astore x) (iloadx)
 * ----->
 * ...A
 * return (astore x) (iloadx)
 * Keep the element in stack for next usage.
 * A should not include another load x and should not have any goto,label and comparison
 * NOTE: IS NOT SOUND. IGNORED!
*/
int remove_storeloadcouple(CODE **c){
  int x1, x2;
  int dump;
  CODE *p = *c;
  if(is_astore(p, &x1) && is_aload(next(p),&x2)){
    if(x1 == x2){
      p = next(next(p));
      while(!is_return(p) && !is_ireturn(p) && !is_areturn(p)){
        if(is_aload(p, &x2) && x1 == x2){
          return 0;
        }
        else if(is_astore(p, &x2) && x1 == x2){
          break;
        }
        else if(stack_effect(p,&dump,&dump,&dump) != 0){
          return 0;
        }
        p = next(p);
      }
      return replace(c,2, NULL);
    }
  }
  else if(is_istore(p, &x1) && is_iload(next(p),&x2)){
    if(x1 == x2){
      p = next(next(p));
      while(!is_return(p) && !is_ireturn(p) && !is_areturn(p)){
        if(is_iload(p, &x2) && x1 == x2){
          return 0;
        }
        else if(is_istore(p, &x2) && x1 == x2){
          break;
        }
        else if(stack_effect(p,&dump,&dump,&dump) != 0){
          return 0;
        }
        p = next(p);
      }
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
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(negative_increment);
	ADD_PATTERN(simplify_goto_goto);
  ADD_PATTERN(simplify_same_instruction_label);
  ADD_PATTERN(more_multiplication_simplification);
	ADD_PATTERN(add_constants);
  ADD_PATTERN(simplify_dup_pop);
  ADD_PATTERN(simplify_swap);
	ADD_PATTERN(remove_storeloadcouple);
  ADD_PATTERN(commutativity);
  ADD_PATTERN(ifsimplify);
/*
  ADD_PATTERN(simplify_istore);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(simplify_multiplication_right);
	ADD_PATTERN(remove_storeloadcouple);
  ADD_PATTERN(simplify_istore);
	ADD_PATTERN(simplify_astore);
	ADD_PATTERN(positive_increment);
	ADD_PATTERN(simplify_goto_goto);
	ADD_PATTERN(add_constants);
	ADD_PATTERN(mul_constants);
  */

}
