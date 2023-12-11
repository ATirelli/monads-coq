
Require Import Monads.FunctorApplicativeMonad.
Require Import NPeano Arith Bool String List.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Definition state_comp(s:Type)(A:Type) := s -> (A*s).

Definition state_comp_map {s} {a b} (f : a -> b) (r : state_comp s a)
  : (state_comp s b):=
fun x => (f (fst (r x)),snd(r x)).


Lemma state_functor_identity {a} {s} (r : state_comp s a)
  : state_comp_map id r = id r.
Proof. intros. unfold state_comp_map.  apply functional_extensionality. intros. 
unfold id.  destruct (r x). auto. Qed.

Lemma state_functor_composition_identity {a b c} {s}
  (u : b -> c) (v : a -> b) (r : state_comp s a)
  : state_comp_map  (u <<< v) r = ((state_comp_map  u) <<< (state_comp_map  v)) r.
Proof. unfold state_comp_map. apply functional_extensionality. intros. unfold compose.
destruct (r x). Show Proof. auto. Qed.


#[program]
Instance state_Functor (s : Type) 
  : Functor (state_comp s ) :=
  { map := @state_comp_map s  
  }.
  
Next Obligation. apply state_functor_identity. Defined

Definition state_comp_apply {s}{a b} (f : state_comp s (a -> b)) (fs : state_comp s a)
  : state_comp s b := 
  fun s => let (x, s'):= fs s in let (g, s''):= f s' in (g x, s'').

Definition state_comp_pure {s} {a}(x:a) : state_comp s a :=
fun s => (x, s).

Lemma state_comp_applicative_identity {s} {a}
  (v : state_comp s  a):
  state_comp_apply (state_comp_pure id) v = v.
  Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
destruct (v x). unfold state_comp_pure. auto. Qed.

Lemma state_comp_applicative_homomorphism {s} {a b} (v : a -> b) (x : a)
  : state_comp_apply (state_comp_pure v) (state_comp_pure x) = state_comp_pure (s:=s) (v x).
Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
unfold state_comp_pure. auto. Qed.

Lemma state_comp_applicative_interchange {s}{a b}(u : state_comp s (a -> b)) (y : a)
  : state_comp_apply u (state_comp_pure y) = state_comp_apply (state_comp_pure (fun z : a -> b => z y)) u.

Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
unfold state_comp_pure. auto. Qed.

#[program]
Instance state_Applicative {s}
  : Applicative (state_comp s) :=
  { pure := @state_comp_pure s 
  ; apply := @state_comp_apply s 
  }.
  
Next Obligation. apply state_comp_applicative_identity. Defined.
Next Obligation. unfold state_comp_apply, state_comp_pure.
apply functional_extensionality. intros.  destruct (w x). destruct (v s0). 
destruct (u s1). auto. Defined.
Next Obligation. unfold state_comp_apply, state_comp_pure, state_comp_map.
apply functional_extensionality. intros. destruct (x x0). auto. Defined.

Definition state_comp_bind {s} {a b}
  (r : state_comp s a) (f : a -> state_comp s b)
  : state_comp s b :=
  fun s => 
              let (v, s') := r s in 
              f v s'.

Lemma state_bind_associativity {s} {a b c} 
  (f : state_comp s a) (g : a -> state_comp s b) (h : b -> state_comp s c)
  : state_comp_bind (state_comp_bind f g) h = 
  state_comp_bind f (fun x : a => state_comp_bind (g x) h).
Proof. unfold state_comp_bind. apply functional_extensionality. intros. 
destruct (f x). destruct (g a0). trivial. Qed.

#[program]
Instance state_comp_Monad {s}
  : Monad (state_comp s) :=
  { bind := @state_comp_bind s
  }.
  
Next Obligation. unfold state_comp_bind, state_comp_pure. 
apply functional_extensionality. intros.
destruct (x x0). trivial. Defined.
Next Obligation. apply state_bind_associativity. Defined.
Next Obligation. unfold state_comp_bind, state_comp_map, state_comp_pure.
apply functional_extensionality. intros. destruct (x x0). trivial. Defined.





