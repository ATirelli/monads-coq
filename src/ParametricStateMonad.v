Add LoadPath "./" as Monads .
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
destruct (r x). auto. Qed.


#[program]
Instance state_Functor (s : Type) 
  : Functor (state_comp s ) :=
  { map := @state_comp_map s  
  }.
  
Next Obligation. apply state_functor_identity. Defined.

Definition state_comp_apply {s} {a b} (f : state_comp s (a -> b)) (fs : state_comp s a)
  : state_comp s b := 
  fun s => let (x, s'):= fs s in let (g, s''):= f s' in (g x, s'').

Definition state_comp_pure {s}{a}(x:a): state_comp s a :=
fun s => (x, s).

Lemma state_applicative_identity {s}{a} (v : state_comp s a):
  state_comp_apply (state_comp_pure id) v = v.
Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
destruct (v x). unfold state_comp_pure. auto. Qed.



