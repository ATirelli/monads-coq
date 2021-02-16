Add LoadPath "./" as Monads .
Require Import Monads.FunctorApplicativeMonad.
Require Import NPeano Arith Bool String List.

Lemma app_empty_str: forall (s:string), (s ++ "")%string = s.
Proof. induction s. - simpl. reflexivity.
                    - simpl. rewrite -> IHs. trivial. Qed.

Lemma app_assoc_string: forall (s s1 s2: string), append (append s s1) s2 = append s (append s1 s2).
Proof. intros s s1. induction s.
- intros. simpl. reflexivity.
- intros. simpl. rewrite IHs. reflexivity. Qed.

Definition output(A:Type):Type := string*A.


Definition output_map {a b} (f : a -> b) (r : output a): (output b):=
let (s, x) := r in (s, f x).


Lemma output_functor_identity {a} (r : output a)
  : output_map id r = id r.
Proof. unfold output_map. destruct r. trivial. Qed.

Lemma output_functor_composition_identity {a b c} 
  (u : b -> c) (v : a -> b) (r : output a)
  : output_map  (u <<< v) r = ((output_map  u) <<< (output_map  v)) r.
Proof. unfold output_map. destruct r. trivial. Qed.

#[program]
Instance output_Functor: Functor (output) :=
  { map := @output_map  
  }.
  
Next Obligation. apply output_functor_identity. Defined.
Next Obligation. apply output_functor_composition_identity. Defined.

Definition output_apply{a b} (f : output (a -> b)) (fs : output a): output b := 
let (s, x):= fs in let (t, g):=f in (append s t, g x).

Definition output_pure {a}(x:a) : output a := (""%string,x).

Lemma output_applicative_identity {a} (v : output a): output_apply (output_pure id) v = v.
Proof. unfold output_apply, output_pure. destruct v. rewrite app_empty_str. trivial. Qed.

Lemma output_applicative_homomorphism {a b} (v : a -> b) (x : a)
  : output_apply (output_pure v) (output_pure x) = output_pure (v x).
Proof. unfold output_apply, output_pure. rewrite app_empty_str. trivial. Qed.

Lemma output_applicative_interchange {a b}(u : output (a -> b)) (y : a)
  : output_apply u (output_pure y) = output_apply (output_pure (fun z : a -> b => z y)) u.
Proof. unfold output_apply, output_pure. destruct u. simpl. rewrite app_empty_str. trivial. Qed.

#[program]
Instance output_Applicative 
  : Applicative (output ) :=
  { pure := @output_pure 
  ; apply := @output_apply  
  }.
  
Next Obligation. apply output_applicative_identity. Defined.
Next Obligation. unfold output_apply, output_pure. destruct u; destruct v; destruct w.
rewrite app_empty_str. rewrite app_assoc_string. trivial. Defined.
Next Obligation. unfold output_apply, output_pure. destruct u. rewrite app_empty_str. trivial. Defined.
Next Obligation. unfold output_map, output_apply, output_pure. destruct x.
rewrite app_empty_str. trivial. Defined.

Definition output_bind {a b} (r : output a) (f : a -> output b): output b :=
let (s, x):= r in
           let (t, y):= f x in 
           (append s t, y).
            
Lemma output_bind_associativity {a b c}(f: output a)(g : a -> output b)(h : b -> output c)
  : output_bind (output_bind f g) h = output_bind f (fun x : a => output_bind (g x) h).
Proof. unfold output_bind. destruct f. try destruct (g a0). destruct (h b0). 
rewrite app_assoc_string. trivial. Qed.

#[program]
Instance output_Monad : Monad (output) :=
  { bind := @output_bind 
  }.
  
Next Obligation. destruct (f x). trivial. Defined.
Next Obligation. unfold output_bind, output_pure. destruct x. rewrite app_empty_str. trivial. Defined.
Next Obligation. apply output_bind_associativity. Defined.
Next Obligation. unfold output_map, output_bind, output_pure. destruct x.
rewrite app_empty_str. trivial. Defined.



 