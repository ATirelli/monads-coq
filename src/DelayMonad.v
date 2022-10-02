Set Implicit Arguments.
Add LoadPath "./" as Monads .

Require Import Monads.Tactics.
Require Import Monads.FunctorApplicativeMonad.




CoInductive Partial A: Type :=
| rtrn : A -> Partial A
| step : Partial A -> Partial A.

Ltac findDestr := match goal with
                    | [ |- context[match ?E with rtrn _ => _ | step _ => _ end] ] =>
                      match E with
                        | context[match _ with rtrn _ => _ | step _ => _ end] => fail 1
                        | _ => destruct E
                      end
                  end.

CoFixpoint partial_map  {a b} (f : a -> b) (x : Partial a): Partial b := 
match x with 
| rtrn y => rtrn (f y)
| step t => step (partial_map f t) end.


CoFixpoint partial_apply {a b} (f : Partial (a -> b)) (x : Partial a): Partial b := 
match x with 
 | rtrn y => match f with 
                              | rtrn g => rtrn (g y)
                              | step t => step (partial_apply t x) end
| step r => step (partial_apply f r) end.

CoFixpoint partial_bind {a b} (f: a -> Partial b) (x: Partial a): Partial b := 
match x with  
| rtrn y => f y 
| step t => step (partial_bind f t) end.

Definition partial_ret {a} (x: a): Partial a := rtrn x.


CoInductive Diverge {A}: Partial A -> Prop :=
  diverge : forall x:Partial A, Diverge x -> Diverge (step x).


Definition frob {A}(x: Partial A) :=
match x with 
| rtrn y => rtrn y
| step t => step t end.

Lemma frob_eq {A}: forall (x: Partial A), x = frob x.
Proof. destruct x; reflexivity. Qed.

CoInductive bisim A : Partial A -> Partial A -> Prop :=
| BisimRtrn : forall x, bisim (rtrn x) (rtrn x)
| BisimStepL : forall m1 m2, bisim m1 m2 -> bisim (step m1) m2
| BisimStepR : forall m1 m2, bisim m1 m2 -> bisim m1 (step m2).

Section bisim_is_unique.
Variable A : Type.
Variable P : Partial A -> Partial A -> Prop.

Hypothesis H : forall m1 m2, P m1 m2
    -> match m1, m2 with
         | rtrn x1, rtrn x2 => x1 = x2
         | step m1', step m2' => P m1' m2'
         | step m1', _ => P m1' m2
         | _, step m2' => P m1 m2'
       end.

Theorem bisim_is_unique : forall m1 m2, P m1 m2 -> bisim m1 m2.
Proof. cofix CIH.
intros. destruct m1.
destruct m2.
apply H in H0. rewrite H0. constructor.
apply H in H0. apply CIH in H0. constructor. assumption.
destruct m2.
apply H in H0. apply CIH in H0. constructor. assumption.
constructor. constructor. apply H in H0. apply CIH in H0. assumption.
Qed.
End bisim_is_unique.

Theorem partial_bisim_frob : forall A (m1 m2 : Partial A),
  bisim (frob m1) (frob m2) -> bisim m1 m2.
Proof. intros. assert (frob m1 = m1). rewrite frob_eq. reflexivity.
assert (frob m2 = m2). rewrite frob_eq. reflexivity. rewrite <- H0. rewrite <- H1. assumption. Qed.

Theorem bisim_refl : forall A (m : Partial A), bisim m m.
Proof. intros. apply (bisim_is_unique (fun m1 m2 => m1 = m2)).
- destruct m1. 
    + destruct m2. 
     * intros. inversion H. reflexivity.
     * intros. inversion H.
    + destruct m2.
     * intros. inversion H.
     * intros. inversion H. reflexivity.
- reflexivity. Qed.

Theorem bindleft_identity : forall A B (a : A) (f : A -> Partial B),
  bisim (partial_bind f (rtrn a)) (f a).
Proof. intros. apply partial_bisim_frob. simpl. destruct (f a); simpl; apply bisim_refl. Qed.


(* Functor axioms *) 
Theorem map_id: forall A (m: Partial A), bisim (partial_map id m) m.
intros. apply (bisim_is_unique (fun m1 m2 => m1 = partial_map id m2));
crush; findDestr; reflexivity. Qed.

Theorem map_assoc: forall A B C (m: Partial A) (f: A -> B) (g: B -> C), 
bisim (partial_map (g <<< f) m) (partial_map g (partial_map f m)).
Proof.
intros. 
apply (bisim_is_unique (fun m1 m2 => (exists m,
    m1 = partial_map (f>>>g) m 
 /\ m2 = (partial_map g (partial_map f m))
  \/ m1 = m2))); crush; auto; repeat (findDestr; crush; auto).
 - exists x. left. split; reflexivity.
 - exists x. right. reflexivity.
 - exists m. left. split; reflexivity. Qed.


Theorem bindright_identity : forall A (m : Partial A),
  bisim (partial_bind partial_ret m) m.
Proof. intros. apply (bisim_is_unique (fun m1 m2 => m1 = partial_bind partial_ret m2)); 
crush; findDestr; reflexivity.
Qed.


Theorem bind_assoc : forall A B C (m : Partial A) (f : A -> Partial B) (g : B -> Partial C),
  bisim (partial_bind g (partial_bind  f m)) (partial_bind (fun x => partial_bind g (f x)) m).
Proof. 
intros.
 apply (bisim_is_unique (fun m1 m2 => (exists m,
    m1 = partial_bind g (partial_bind f m)
    /\ m2 = partial_bind (fun x => partial_bind g (f x) ) m)
  \/ m1 = m2))
; crush; eauto; repeat (findDestr; crush; eauto).
Qed.


