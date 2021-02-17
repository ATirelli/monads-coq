Add LoadPath "./" as Monads .
(*Require Import Monads.StateMonad.*)
Require Import Monads.FunctorApplicativeMonad.

From Coq Require Import FunctionalExtensionality Program.Basics.

Set Universe Polymorphism.

#[local]
Close Scope nat_scope.
#[local]
Open Scope prelude_scope.

(** * Definition *)

Definition state_t (s : Type) (m : Type -> Type) (a : Type) : Type :=
  s -> m (a * s).

Bind Scope monad_scope with state_t.

Definition run_state_t {m s a} (r : state_t s m a) (x : s) : m (a * s) :=
  r x.
  

Definition eval_state_t {m s a} `{Monad m} (r : state_t s m a) (x : s) : m a :=
  map fst (r x).

Definition exec_state_t {m s a} `{Monad m} (r : state_t s m a) (x : s) : m s :=
  map snd (r x).

(** * State Monad *)

Definition state_map {m s} `{Monad m} {a b} (f : a -> b) (r : state_t s m a)
  : state_t s m b :=
  fun* x => (fun o => (f (fst o), snd o)) <$> r x.

Lemma state_functor_identity {m s a} `{Monad m} 
  (r : state_t s m a)
  : state_map id r = id r.

Proof. Admitted. 