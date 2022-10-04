Require Import Nat.


Inductive Fin: nat -> Type :=
  fin_zero: forall n:nat, Fin (S n)
| fin_succ: forall n:nat, Fin n -> Fin (S n).

Fixpoint finite_nat (n:nat)(i:Fin n): nat :=
match i with
  fin_zero n => 0
| fin_succ n i' => S (finite_nat n i')
end.

Inductive vec (A:Type): nat -> Type :=
  vec_nil: vec A 0
| vec_cons: forall n:nat, vec A n -> A -> vec A (S n).


Definition vector_head: forall (A:Type)(n:nat),(vec A (S n)) -> A.
intros A n v; inversion_clear v.
exact X0.
Defined.

Arguments vector_head {A n}.

Definition vector_tail: forall (A:Type)(n:nat),(vec A (S n)) -> (vec A n).
intros A n v; inversion_clear v.
exact X.
Qed.

Arguments vector_tail {A n}.

Fixpoint lookup {n: nat} {A: Type} (x: Fin n) (v: vec A n): A :=
match x with 
| fin_zero n => (vector_head v)
| fin_succ n i  => lookup i vector_tail v end. 

lookup : \u2200 {a n} {A : Set a} \u2192 Fin n \u2192 Vec A n \u2192 A
lookup zero    (x \u2237 xs) = x
lookup (suc i) (x \u2237 xs) = lookup i xs
