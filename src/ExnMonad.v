Add LoadPath "./" as Monads .
Require Import Monads.FunctorApplicativeMonad.
Require Import NPeano Arith Bool String List.

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

Lemma exn_functor_identity {a} (r : exn a)
  : exn_map id r = id r.
Proof. unfold exn_map. destruct r; trivial. Qed.

Lemma exn_functor_composition_identity {a b c} 
  (u : b -> c) (v : a -> b) (r : exn a)
  : exn_map  (u <<< v) r = ((exn_map  u) <<< (exn_map  v)) r.
Proof. unfold exn_map. destruct r; trivial. Qed.

#[program]
Instance exn_Functor: Functor (exn) :=
  { map := @exn_map  
  }.
  
Next Obligation. apply exn_functor_identity. Defined.
Next Obligation. apply exn_functor_composition_identity. Defined.

Definition exn_apply{a b} (f : exn (a -> b)) (fs : exn a): exn b := 
match fs with 
| Fail s => Fail s
| Result x => match f with 
                | Result g => Result (g x)
                | Fail t => Fail t end end .

Definition exn_pure {a}(x:a) : exn a := Result x.

Lemma exn_applicative_identity {a} (v : exn a): exn_apply (exn_pure id) v = v.
Proof. unfold exn_apply, exn_pure. destruct v; trivial. Qed.

Lemma exn_applicative_homomorphism {a b} (v : a -> b) (x : a)
  : exn_apply (exn_pure v) (exn_pure x) = exn_pure (v x).
Proof. unfold exn_apply, exn_pure. trivial. Qed.

Lemma exn_applicative_interchange {a b}(u : exn (a -> b)) (y : a)
  : exn_apply u (exn_pure y) = exn_apply (exn_pure (fun z : a -> b => z y)) u.
Proof. unfold exn_apply, exn_pure. destruct u; trivial. Qed.

#[program]
Instance exn_Applicative 
  : Applicative (exn ) :=
  { pure := @exn_pure 
  ; apply := @exn_apply  
  }.
  
Next Obligation. apply exn_applicative_identity. Defined.
Next Obligation. unfold exn_apply. destruct u; destruct v; destruct w; auto. Defined.

Definition exn_bind {a b} (r : exn a) (f : a -> exn b): exn b :=
match r with 
              | Result y => f y
              | Fail s => Fail s
            end.
            
Lemma exn_bind_associativity {a b c}(f: exn a)(g : a -> exn b)(h : b -> exn c)
  : exn_bind (exn_bind f g) h = exn_bind f (fun x : a => exn_bind (g x) h).
Proof. unfold exn_bind. destruct f; try destruct (g a0); try auto. Qed.

#[program]
Instance exn_Monad : Monad (exn) :=
  { bind := @exn_bind 
  }.
  
Next Obligation. unfold exn_bind, exn_pure. destruct x; reflexivity. Defined.
Next Obligation. apply exn_bind_associativity. Defined.




 