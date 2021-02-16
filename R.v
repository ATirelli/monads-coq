Require Import NPeano Arith Bool String List.
Require Import Coq.Logic.FunctionalExtensionality.
Local Open Scope string.

 Set Implicit Arguments. 

Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

(* packaging the monadic laws*)

Class MonadProof (M : Type -> Type) {H : Monad M} := 
  {
  left_id_monad : forall {A B:Type} (x:A) (f:A -> M B), bind (ret x) f = f x;
  right_id_monad : forall {A B:Type} (c:M A), bind c ret = c     ;
   assoc_monad : forall {A B C} (c:M A) (f:A->M B) (g:B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)                                                      
  }.


Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Definition state := string -> nat.

Definition default_state (n : nat) : state :=
  (fun _ => n).

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition state_update  (m : state )
                    (x : string) (v : nat) :=
  fun x' => if eqb_string x x' then v else m x'.

Notation "'_' '!->' v" := (default_state v)
  (at level 100, right associativity).

Definition empty_st := (_ !-> 0).

Definition read_comp (A:Type) := state -> A.

Definition read (x:string) : read_comp nat := 
  fun s => (s x).

Instance ReadMonad : Monad read_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => x) ; 
  bind := fun {A B:Type} (c : read_comp A) (f: A -> read_comp B) => 
            fun (s:state) => 
              f (c s) s
}.


Instance ReadMonadP : MonadProof.
constructor;  intros;  apply functional_extensionality;   trivial.
Defined.


Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)             
  | APlus (a1 a2 : aexp)
  | EqExp (a1 a2: aexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

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
Definition X:string:="x".
Definition Y:string:="y".
Definition Z:string:="z".


Fixpoint aeval (a : aexp) : read_comp nat :=
  match a with
  | ANum n       => ret n
  | AId x        => read x                                
  | <{a1 + a2}>  => n1 <- aeval a1 ;; n2 <- aeval a2 ;; ret (n1 + n2)
  | <{a1 == a2}> => n1 <- aeval a1 ;; n2 <- aeval a2 ;; 
                    if (n1 =? n2)%nat  then  ret 0 else ret 1
  end.

Check (aeval <{1==0}> empty_st) .
Print aeval.
Compute (aeval <{1==0}> empty_st) .
Compute (aeval <{1==1}> empty_st).
Compute (aeval <{X==Y}> empty_st).
