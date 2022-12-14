Require Import Monads.FunctorApplicativeMonad.
Require Import Monads.StateTransformer.
Require Import Monads.ExnMonad.
Require Import NPeano Arith Bool String List.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Definition state:= string -> nat.
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition state_update  (m : state )
                    (x : string) (v : nat) :=
  fun x' => if eqb_string x x' then v else m x'.
  
Definition newarray (n : nat) : state :=
  (fun _ => n).

Notation "'_' '!->' v" := (newarray v)
  (at level 100, right associativity).

Definition empty_st := (_ !-> 0).


Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)             
  | APlus (a1 a2 : exp)
  | ADiv (a1 a2: exp)
  | EqExp (a1 a2: exp).

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x / y" := (ADiv x y) (in custom com at level 50, left associativity).
Notation "x == y" := (EqExp x y) (in custom com at level 50, left associativity).
Open Scope com_scope.

Definition X:string:="x"%string.
Definition Y:string:="y"%string.
Definition Z:string:="z"%string.

Inductive com : Type :=
  | CSkip 
  | CAss (x : string) (a : exp)
  | CSeq (c1 c2 : com)
  | CIf (a: exp) (c1 c2 : com)
  | CWhile (a: exp) (c: com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'd' y 'end'" :=
         (CWhile x y)
   (in custom com at level 89, x at level 99, y at level 99) : com_scope.
   
Definition exn_state:= state_t state exn.
Definition eval_exn_state :=exn_state nat.
Definition exec_exn_state :=exn_state unit.

Definition fetch (x:string) : eval_exn_state := 
  fun s =>  Result (s x, s).
Definition assign (x:string) (n:nat) : exec_exn_state := 
  fun s => Result (tt, state_update s x n).
  
Fixpoint eval (a : exp) : eval_exn_state :=
  match a with
  | ANum n       => pure n
  | AId x        => fetch x  
  | <{a1 + a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; pure (n1 + n2)
  | <{a1 / a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; match n2 with 
                                                              | 0 => fun s => Fail "Division by zero!"
                                                              | _ => pure (n1 / n2) end
  | <{a1 == a2}> => n1 <- eval a1 ;; n2 <- eval a2 ;; match (beq_nat n1 n2) with 
                                                                          | true     => pure 0
                                                                          | false    => pure 1
                                                                          end end.

 
Example ex:exp := <{X+Y/Z}>.
Compute  (eval ex (newarray 1)). 
Compute  (eval ex empty_st).  

Fixpoint exec (c: com)(fuel: nat): exec_exn_state :=
match fuel with 
| 0       => fun s => Fail "Gas finished before end of program! Try executing with more gas."
| S fuel' => match c with 
    | <{ skip }>    => pure tt
    | <{ x := a }>  => n <- eval a ;; fun s => Result (tt, state_update s x n)
    | <{c1; c2}>    => x <- (exec c1 fuel');; y <- (exec c2 fuel');; pure tt
    | <{if a then c1 else c2 end}> => n <- eval a ;; match n with 
                                                    | 0 => (exec c1 fuel')
                                                    | _ => (exec c2 fuel') end
    | <{while b d c1 end}> => n <- eval b ;; match n with
                                                    | 0 => x<-(exec c1 fuel');;(exec c fuel')
                                                    | _ => pure tt end 

end end .

Definition fact_in_coq : com :=
  <{ Z := 0;
     Y := 1;
     while X d
       if Y == 5 then 
         X:=1; X:=X/Z 
       else
         Y := Y+1
       end
      end
     }>.
     
Definition eval_on_exn_state(es: exn (unit*state))(s: string): exn  nat:=
match es with 
| Fail str => Fail str 
| Result (a, st) => Result (st s) end. 

Compute  eval_on_exn_state((exec fact_in_coq 2) empty_st) X.


Fixpoint eval_not_t (a : exp) :state-> exn (nat*state) :=
  match a with
  | ANum n       => fun s => Result (n, s)
  | AId x        => fun s => Result (s x, s) 
  | <{a1 + a2}>  => fun s => let n1:=(eval_not_t a1 s) in let n2:= (eval_not_t a2 s) in 
                                match n1 with 
                                  | Fail s    => Fail s
                                  | Result (m1, t) => match n2 with 
                                        | Fail s => Fail s
                                        | Result (m2, t) => Result (m1 + m2, s) end end 
  | <{a1 / a2}>  => fun s => let n1:=(eval_not_t a1 s) in let n2:= (eval_not_t a2 s) in 
                                match n1 with 
                                  | Fail s    => Fail s
                                  | Result (m1, t) => match n2 with 
                                        | Fail s => Fail s
                                        | Result (m2, t) => match m2 with 
                                                 | 0 => Fail "Division by zero!"
                                                 | _ => Result (m1/m2, s) end end end 
  | <{a1 == a2}> => fun s => let n1:=(eval_not_t a1 s) in let n2:= (eval_not_t a2 s) in  
                                match n1 with 
                                  | Fail s    => Fail s
                                  | Result (m1, t) => match n2 with 
                                        | Fail s => Fail s
                                        | Result (m2, t) => match (beq_nat m1 m2) with 
                                                        | true     => Result (0, s)
                                                        | false    => Result (1, s)
                                                                          end end end end .

Compute  (eval ex (newarray 1)). 
Compute  (eval ex empty_st).
Fixpoint exec_no_t (c: com)(fuel: nat): (state -> exn(unit * state)) :=
match fuel with 
| 0       => fun s=> Fail "Gas finished before end of program! Try executing with more gas."
| S fuel' => match c with 
        | <{ skip }>    => fun s => Result (tt, s)
        | <{ x := a }>  => fun s => let m:=(eval_not_t a s) in match m with 
                                                | Result (n, s) => Result (tt, state_update s x n)
                                                | Fail str => Fail str end 
        | <{c1; c2}>    => fun s => let o:= (exec_no_t c1 fuel') in match (o s) with 
                                                | Fail str => Fail str
                                                | Result (a, s') => 
                                                    let o':= (exec_no_t c2 fuel') in (o' s') end 
        | <{if a then c1 else c2 end}> => fun s => let m:=(eval_not_t a s) in match m with
                                                | Fail str => Fail str 
                                                | Result (n, s) => match n with 
                                                          | 0 => (exec_no_t c1 fuel') s
                                                          | _ => (exec_no_t c2 fuel') s end end 
        |<{while b d c1 end}> => fun s => let m:=(eval_not_t b s) in match m with
                                                | Fail str => Fail str
                                                | Result (b1, s) => match b1 with 
                                                        | S _ => Result (tt, s)
                                                        | 0   => match ((exec_no_t c1 fuel') s) with 
                                                               | Result (a, s') => (exec_no_t c fuel') s'
                                                               | Fail str => Fail str end end end 
end end.





