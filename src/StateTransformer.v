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

Lemma pair_fst_snd {a b} (x: a*b): (fst x, snd x) = x.
Proof. destruct x. unfold fst, snd. trivial. Qed.

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
  fun (s0: s) => (bind (r s0) (fun (y:a*s) => pure(f (fst y), snd y))).
    
Print state_map.

Lemma fst_snd_in_monad {a s m} `{Monad m}: 
(fun y : a * s => pure (fst y, snd y)) = (fun y : a * s => pure y).
Proof. apply functional_extensionality; intros; rewrite pair_fst_snd; trivial. Qed.

Lemma state_functor_identity {m s a} `{Monad m} 
  (r : state_t s m a)
  : state_map id r = id r.

Proof. unfold state_map. apply functional_extensionality. intros. unfold id.
rewrite fst_snd_in_monad. apply bind_right_identity. Qed.
 