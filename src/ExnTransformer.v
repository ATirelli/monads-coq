Add LoadPath "./" as Monads .

Require Import Monads.FunctorApplicativeMonad.

From Coq Require Import FunctionalExtensionality Program.Basics String.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Set Universe Polymorphism.

#[local]
Close Scope nat_scope.
#[local]
Open Scope prelude_scope.

(** * Definition *)

Inductive exn(A:Type) : Type := 
| Result : A -> exn A
| Fail : string -> exn A.
Arguments Result {A}.
Arguments Fail {A}.

Definition exn_map {a b} (f : a -> b) (r : exn a)
  : (exn b):=
match r with 
| Result x => Result (f x)
| Fail s => Fail s end.

Definition exn_t  (m : Type -> Type) (a : Type) : Type := m (exn a).

Bind Scope monad_scope with exn_t.

Definition exn_t_map {m} `{Monad m} {a b} (f : a -> b) (r : exn_t m a)
  : exn_t m b := map (exn_map f) r.
  
  
Lemma exn_t_functor_identity {m a} `{Monad m} 
  (r : exn_t m a)
  : exn_t_map id r = id r.


Proof. unfold exn_t_map. assert (H1: exn_map(b:=a) id = id)
by (apply functional_extensionality; intro x; destruct x; auto).
rewrite H1. assert (H2: map(b:=exn a) id = id) by
(apply functional_extensionality; intro x; apply  functor_identity).
rewrite H2. trivial. Qed.

Lemma exn_functor_composition_identity {a b c} 
  (u : b -> c) (v : a -> b) (r : exn a)
  : exn_map  (v >>> u) r = ((exn_map  v) >>> (exn_map  u)) r.
Proof. unfold exn_map. destruct r; trivial. Qed.

Lemma exn_t_functor_composition_identity {m a b c} `{Monad m} 
  (u : b -> c) (v : a -> b) (r : exn_t  m a)
  : exn_t_map (u <<< v) r = ((exn_t_map u) <<< (exn_t_map v)) r.
Proof. unfold exn_t_map. assert (H1:  (exn_map (v>>>u)) = (exn_map v) >>> (exn_map u))
by(apply functional_extensionality; intro; rewrite exn_functor_composition_identity; auto).
rewrite H1. rewrite functor_map_identity. auto. Qed.

#[program]
Instance exn_t_Functor (m :  Type -> Type) `{Monad m} 
  : Functor (exn_t m) :=
  { map := @exn_t_map m  _
  }.

Next Obligation.
  apply exn_t_functor_identity.
Defined.

Next Obligation.
  apply exn_t_functor_composition_identity.
Defined.

Definition exn_apply{a b} (f : exn (a -> b)) (fs : exn a): exn b := 
match fs with 
| Fail s => Fail s
| Result x => match f with 
                | Result g => Result (g x)
                | Fail t => Fail t end end .

Definition exn_t_pure {m} `{Monad m} {a} (x : a) : exn_t m a := pure (Result x).

