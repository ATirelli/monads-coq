Require Import Monads.FunctorApplicativeMonad.

From Coq Require Import FunctionalExtensionality Program.Basics.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Set Universe Polymorphism.

#[local]
Close Scope nat_scope.
#[local]
Open Scope prelude_scope.

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
Print apply.

Definition state_map {m s} `{Monad m} {a b} (f : a -> b) (r : state_t s m a)
  : state_t s m b :=
  fun x => apply (map (fun y => (f (fst y), snd y))) (r x).
    


Lemma fst_snd_in_fun {a s m} `{Monad m}: 
(fun y : a * s =>  (fst y, snd y)) = (fun y : a * s =>  y).
Proof. apply functional_extensionality; intros; rewrite pair_fst_snd; trivial. Qed.

Lemma state_functor_identity {m s a} `{Monad m} 
  (r : state_t s m a)
  : state_map id r = id r.

Proof. unfold state_map. apply functional_extensionality. intros. unfold id.
rewrite fst_snd_in_fun. apply functor_identity. Qed.

Lemma state_functor_composition_identity {m s a b c} `{Monad m} 
  (u : b -> c) (v : a -> b) (r : state_t s m a)
  : state_map (u <<< v) r = ((state_map u) <<< (state_map v)) r.
Proof. unfold state_map. apply functional_extensionality. intros.
change (fun y => ((u <<< v) (fst y), snd y))
    with ((fun y => (v (fst y), snd y)) >>> (fun y : b * s => (u (fst y), snd y))).
    apply functor_map_identity. Qed.

#[program]
Instance state_Functor (m :  Type -> Type) `{Monad m} (s : Type)
  : Functor (state_t s m) :=
  { map := @state_map m s _
  }.

Next Obligation.
  apply state_functor_identity.
Defined.

Next Obligation.
  apply state_functor_composition_identity.
Defined.


Definition state_apply {m s} `{Monad m} {a b}
  (f : state_t s m (a -> b)) (fs : state_t s m a)
  : state_t s m b :=
  fun x => u <- f x ;; v <- fs (snd u);; pure (fst u (fst v), snd v).

Definition state_pure {m s} `{Monad m} {a} (x : a) : state_t s m a :=
  fun s => pure (x, s).

Lemma state_applicative_identity {m s} `{Monad m} {a} (v : state_t s m a):
  state_apply (state_pure id) v = v.
Proof. unfold state_apply, state_pure. apply functional_extensionality. intros.
rewrite bind_left_identity. simpl. unfold id.   
assert (H1: (fun (v0:a*s) => pure (fst v0, snd v0))= (fun v0 =>pure  v0)).
- apply functional_extensionality. intros. destruct x0; auto.
- rewrite H1. apply bind_right_identity. Qed.

Lemma state_applicative_homomorphism {m s} `{Monad m}{a b}
  (v : a -> b) (x : a)
  : state_apply (state_pure v) (state_pure x) = state_pure (m:=m) (s:=s) (v x).

Proof. unfold state_pure, state_apply. apply functional_extensionality. intros.
repeat rewrite bind_left_identity. auto. Qed.

Lemma state_applicative_interchange {m s} `{Monad m} {a b}
  (u : state_t s m (a -> b)) (y : a)
  : state_apply u (state_pure y) = state_apply (state_pure (fun z : a -> b => z y)) u.
Proof. unfold state_apply, state_pure. apply functional_extensionality. intros.
rewrite bind_left_identity. 
match goal with
  | |- bind _ ?f = bind _ ?g =>
    assert (R : f = g); [| now rewrite R ]
  end. apply functional_extensionality. intros. rewrite bind_left_identity. auto. Qed.
  
#[program]
Instance state_Applicative (m : Type -> Type) `{Monad m} (s : Type) 
  : Applicative (state_t s m) :=
  { pure := @state_pure m s _
  ; apply := @state_apply m s _
  }.
  
Next Obligation.
  apply state_applicative_identity.
Defined.

Next Obligation.
apply functional_extensionality. intros.
  unfold state_apply, state_pure.
  repeat rewrite bind_associativity.
  repeat rewrite bind_left_identity.
  repeat rewrite bind_associativity.
  
  match goal with
  | |- bind _ ?f = bind _ ?g => assert (R: f = g); [| now rewrite R ]
  end.
  apply functional_extensionality. intros.
  repeat rewrite bind_associativity.
  repeat rewrite bind_left_identity.
  repeat rewrite bind_associativity.
  
  match goal with
  | |- bind _ ?f = bind _ ?g => assert (R: f = g); [| now rewrite R ]
  end.
  apply functional_extensionality. intros.

  repeat rewrite bind_associativity.
  repeat rewrite bind_left_identity.

  match goal with
  | |- bind _ ?f = bind _ ?g => assert (R: f = g); [| now rewrite R ]
  end.
 apply functional_extensionality. intros.

  unfold compose.
  repeat rewrite bind_left_identity.
  cbn.
  reflexivity.
Defined.

Next Obligation.
  apply state_applicative_homomorphism.
Defined.

Next Obligation.
   apply state_applicative_interchange.
Defined.

Next Obligation.
  unfold state_map, state_pure, state_apply.
  apply functional_extensionality. intros.
  rewrite bind_left_identity. 
  cbn. apply bind_map. Defined.
  
  
(* now we prove that the image under state_t of a monad m is indeed a monad *)

Definition state_bind {m s} `{Monad m} {a b}
  (r : state_t s m a) (f : a -> state_t s m b)
  : state_t s m b :=
  fun x => y <- r x ;; f (fst y) (snd y).

Lemma state_bind_associativity {m s} `{Monad m}  {a b c} 
  (f : state_t s m a) (g : a -> state_t s m b) (h : b -> state_t s m c)
  : state_bind (state_bind f g) h = state_bind f (fun x : a => state_bind (g x) h).
Proof.
  unfold state_bind. apply functional_extensionality. intros.
  rewrite bind_associativity.
  reflexivity.
Qed.

#[program]
Instance state_Monad (m : Type -> Type) `{Monad m} (s : Type) 
  : Monad (state_t s m) :=
  { bind := @state_bind m s _
  }.
  
Next Obligation. unfold state_bind. apply functional_extensionality. intros.
unfold state_pure. apply bind_left_identity. Defined.

Next Obligation. unfold state_bind, state_pure.
assert (R: (fun u : a * s => pure (fst u, snd u)) = fun u : a * s => pure (f:=m) u).
- apply functional_extensionality; intro u; destruct u; auto.
- rewrite R. apply functional_extensionality; intro. apply bind_right_identity. Defined.

Next Obligation.
  apply state_bind_associativity.
Defined.

Next Obligation.
  unfold state_bind, state_map, state_pure.
  apply functional_extensionality; intro.
  apply bind_map. Defined.
  
Print state_Monad.


Definition state_lift {m s} `{Monad m} {a} (x : m a) : state_t s m a :=
  fun s => bind x (fun o => pure (o, s)).


Instance state_MonadTrans (s : Type) : MonadTrans (state_t s) :=
  { lift := fun m H => @state_lift m s H
  }.
 

 