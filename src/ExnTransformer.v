Add LoadPath "./" as Monads .
Require Import Monads.FunctorApplicativeMonad.
Require Import Monads.ExnMonad.
From Coq Require Import FunctionalExtensionality Program.Basics.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Definition exn_t (m : Type -> Type) (a : Type) : Type := m (exn a).


Definition exn_t_map {m} `{Monad m} {a b} (f : a -> b) (r : exn_t m a)
  : exn_t m b := 
bind(m:=m) r (fun y => pure ((exn_map f) y)).
                      
Lemma exn_t_functor_identity {m a} `{Monad m} 
  (r : exn_t m a)
  : exn_t_map id r = id r.
Proof. unfold exn_t_map. 
assert (H1: (fun y : exn a => pure (exn_map id y))= (fun (y: exn a)=> pure y)) by
(apply functional_extensionality; intro; rewrite exn_functor_identity; auto).

Admitted.