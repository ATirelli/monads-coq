Require Import Monads.StateMonad.
Require Import Monads.FunctorApplicativeMonad.
Require Import NPeano Arith Bool String List.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Definition counter := nat.
Definition program_counter := (state_comp counter nat).

Inductive tm := 
| Con : nat -> tm
| Div : tm -> tm -> tm.

Example answer: tm := (Div (Div (Con 1972) (Con 2 )) (Con 23 )).
Example error: tm := (Div (Con 1)(Con 0)).


Fixpoint eval_and_count (t:tm) : program_counter  := 
  match t with 
  | Con n => pure n 
  | Div t1 t2  =>
      n1 <- eval_and_count t1 ;; 
      n2 <- eval_and_count t2 ;; 
      fun (s:counter) => ( n1/n2, s+1 )
      end.

Compute eval_and_count answer 0.

(* = (42, 2)
     : nat * counter *)
Compute eval_and_count error 0.

(*  = (0, 1)
     : nat * counter
*)


Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)             
  | APlus (a1 a2 : exp)
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
Notation "x == y" := (EqExp x y) (in custom com at level 50, left associativity).
Open Scope com_scope.

Definition X:string:="x"%string.
Definition Y:string:="y"%string.
Definition Z:string:="z"%string.

(** As far as commands go, we consider: 
- the "skip" command, which performs no action
- the assignment command, which assigns an expression to a variable
- the sequence of two commands
- the [If] statement.

*)

Inductive com : Type :=
  | CSkip 
  | CAss (x : string) (a : exp)
  | CSeq (c1 c2 : com)
  | CIf (a: exp) (c1 c2 : com).

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
            
Definition state:= string -> nat.

Definition eval_state :=state_comp state nat.

Definition exec_state :=state_comp state unit.

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

Definition fetch (x:string) : eval_state := 
  fun s => (s x, s).
  
Definition assign (x:string) (n:nat) : exec_state := 
  fun s => (tt, state_update s x n).

Fixpoint eval (a : exp) : eval_state :=
  match a with
  | ANum n       => pure n
  | AId x        => fetch x                                
  | <{a1 + a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; pure (n1 + n2)
  | <{a1 == a2}> => n1 <- eval a1 ;; n2 <- eval a2 ;; match (beq_nat n1 n2) with 
                                                                          | true     => pure 0
                                                                          | false    => pure 1
                                                                          end end.


Fixpoint exec (c : com) : exec_state :=
  match c with
  | <{ skip }>                    => pure tt
  | <{ x := a }>                  => n <- eval a ;; assign x n 
  | <{c1; c2}>                    => x <- exec c1 ;; y <- exec c2 ;; pure tt
  | <{if a then c1 else c2 end}>  => n <- eval a ;;
                                    match n with 
                                      | 0 => exec c1
                                      | _ => exec c2 
                                    end
  end.
  

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     if Z == 0 then
       Y := Y + Z
      else
       Z := Z + 1
     end
     }>.

Compute snd (exec fact_in_coq empty_st) X.
Compute snd (exec fact_in_coq empty_st) Y.














