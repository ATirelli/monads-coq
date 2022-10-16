Require Import Arith List Monads.Tactics.

Set Implicit Arguments.
Set Asymmetric Patterns.


  Variable A : Type.

  Inductive ilist : nat -> Type :=
  | INil : ilist O
  | ICons : forall n, A -> ilist n -> ilist (S n).

  Definition hd n (ls : ilist (S n)) :=
    match ls in ilist n' return match n' with
                                  | O => unit
                                  | S _ => A
                                end with
      | INil => tt
      | ICons _ x _ => x
    end.
  Definition tl n (ls : ilist (S n)) :=
    match ls in ilist n' return match n' with
                                  | O => unit
                                  | S n => ilist n
                                end with
      | INil => tt
      | ICons _ _ ls' => ls'
    end.

  Inductive fin : nat -> Set :=
  | First : forall n, fin (S n)
  | Next : forall n, fin n -> fin (S n).

  Fixpoint get n (ls : ilist n) : fin n -> A :=
    match ls with
      | INil => fun idx =>
        match idx in fin n' return (match n' with
                                        | O => A
                                        | S _ => unit
                                      end) with
          | First _ => tt
          | Next _ _ => tt
        end
      | ICons _ x ls' => fun idx =>
        match idx in fin n' return (fin (pred n') -> A) -> A with
          | First _ => fun _ => x
          | Next _ idx' => fun get_ls' => get_ls' idx'
        end (get ls')
    end.