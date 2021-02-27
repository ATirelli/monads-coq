Add LoadPath "./" as Monads .
Require Import Monads.FunctorApplicativeMonad.
Require Import Monads.StateMonad.
Require Import Monads.ExnTransformer.
Require Import NPeano Arith Bool String List.

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
   
Definition exn_state:= exn_t (state_comp state).
Definition eval_exn_state :=exn_state nat.
Definition exec_exn_state :=exn_state unit.

Definition fetch (x:string) : eval_exn_state := 
  fun s =>  (Result (s x), s).
Definition assign (x:string) (n:nat) : exec_exn_state := 
  fun s => (Result tt, state_update s x n).
  
Fixpoint eval (a : exp) : eval_exn_state :=
  match a with
  | ANum n       => pure n
  | AId x        => fetch x  
  | <{a1 + a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; pure (n1 + n2)
  | <{a1 / a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; match n2 with 
                                                              | 0 => fun s => (Fail "Division by zero!", s)
                                                              | _ => pure (n1 / n2) end
  | <{a1 == a2}> => n1 <- eval a1 ;; n2 <- eval a2 ;; match (beq_nat n1 n2) with 
                                                                          | true     => pure 0
                                                                          | false    => pure 1
                                                                          end end.
 
Example ex:exp := <{X+Y/Z}>.
Compute fst (eval ex (newarray 1)). 
Compute fst (eval ex empty_st).  

