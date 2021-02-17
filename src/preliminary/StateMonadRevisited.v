Add LoadPath "./" as Monads .
Require Import Monads.FunctorApplicativeMonad.
Require Import NPeano Arith Bool String List.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.
  

Definition state := string -> nat.

Definition newarray (n : nat) : state :=
  (fun _ => n).

Notation "'_' '!->' v" := (newarray v)
  (at level 100, right associativity).

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition state_update  (m : state )
                    (x : string) (v : nat) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition state_comp(A:Type) := state -> (A*state).

Definition assign (x:string) (n:nat) : state_comp unit := 
  fun s => (tt, state_update s x n).

Definition fetch (x:string) : state_comp nat := 
  fun s => (s x, s).


Definition state_comp_map {a b: Type} (f : a -> b) (r : state_comp a)
  : (state_comp b ):=
fun s => (f (fst (r s)),snd(r s)).


Lemma state_functor_identity {a}  (r : state_comp a)
  : state_comp_map id r = id r.
Proof. intros. unfold state_comp_map.  apply functional_extensionality. intros. 
unfold id.  destruct (r x). auto. Qed.


Lemma state_functor_composition_identity {a b c}
  (u : b -> c) (v : a -> b) (r : state_comp a)
  : state_comp_map (u <<< v) r = ((state_comp_map u) <<< (state_comp_map v)) r.
Proof. unfold state_comp_map. apply functional_extensionality. intros. unfold compose.
destruct (r x). auto. Qed.

Print Functor.
Program Instance state_comp_functor: (Functor state_comp ) := {
map:= @state_comp_map
}.
Next Obligation. apply state_functor_identity.
Defined.

Definition state_comp_apply {a b} (f : state_comp (a -> b)) (fs : state_comp a)
  : state_comp b := 
  fun s => let (x, s'):= fs s in let (g, s''):= f s' in (g x, s'').

Definition state_comp_pure {a}(x:a): state_comp a :=
fun s => (x, s).

Lemma state_applicative_identity {a} (v : state_comp a):
  state_comp_apply (state_comp_pure id) v = v.
Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
destruct (v x). unfold state_comp_pure. auto. Qed.

Lemma state_applicative_homomorphism {a b} 
  (v : a -> b) (x : a)
  : state_comp_apply (state_comp_pure v) (state_comp_pure x)
   = state_comp_pure   (v x).
Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
unfold state_comp_pure. auto. Qed.

Lemma state_applicative_interchange  {a b} 
  (u : state_comp (a -> b)) (y : a)
  : state_comp_apply u (state_comp_pure y) 
  = state_comp_apply (state_comp_pure (fun z : a -> b => z y)) u.
Proof. unfold state_comp_apply. apply functional_extensionality. intros. 
unfold state_comp_pure. auto. Qed.

#[program]
Instance state_Applicative 
  : Applicative (state_comp) :=
  { pure := @state_comp_pure 
  ; apply := @state_comp_apply
  }.
Next Obligation. apply state_applicative_identity. Defined.
Next Obligation. unfold state_comp_apply, state_comp_pure.
apply functional_extensionality. intros. destruct (w x). destruct (v s). 
destruct (u s0). auto. Defined.
Next Obligation. unfold state_comp_apply, state_comp_pure, state_comp_map.
apply functional_extensionality. intros. destruct (x x0). auto. Defined.


Definition state_comp_bind {a b}
  (r : state_comp a) (f : a -> state_comp b)
  : state_comp b :=
  fun (s:state) => 
              let (v, s') := r s in 
              f v s'.

Lemma state_bind_associativity  {a b c} 
  (f : state_comp a) (g : a -> state_comp b) (h : b -> state_comp c)
  : state_comp_bind (state_comp_bind f g) h = 
  state_comp_bind f (fun x : a => state_comp_bind (g x) h).
Proof. unfold state_comp_bind. apply functional_extensionality. intros. 
destruct (f x). destruct (g a0). trivial. Qed.

#[program]
Instance state_comp_Monad 
  : Monad (state_comp ) :=
  { bind := @state_comp_bind
  }.
Next Obligation. unfold state_comp_bind, state_comp_pure. 
apply functional_extensionality. intros.
destruct (x x0). trivial. Defined.
Next Obligation. apply state_bind_associativity. Defined.
Next Obligation. unfold state_comp_bind, state_comp_map, state_comp_pure.
apply functional_extensionality. intros. destruct (x x0). trivial. Defined.

Class MonadState (s : Type) (m : Type -> Type) :=
  { monadstate_is_monad :> Monad m
  ; put : s -> m unit
  ; get : m s
  }.

 
Inductive exp : Type := 
  | ANum (n : nat)
  | AId (x : string)             
  | APlus (a1 a2 : exp)
  | EqExp (a1 a2: exp).

Coercion AId : string >-> exp.
Coercion ANum : nat >-> exp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x == y" := (EqExp x y) (in custom com at level 50, left associativity).
Open Scope com_scope.

Definition X:string:="x"%string.
Definition Y:string:="y"%string.
Definition Z:string:="z"%string.

(** As far as commands go, we consider: 
- the "skip" command, which performs no action
- the assignment command, which assigns an expression to a variable
- the sequence of two commands
- the [If] statement.

*)

Inductive com : Type :=
  | CSkip 
  | CAss (x : string) (a : exp)
  | CSeq (c1 c2 : com)
  | CIf (a: exp) (c1 c2 : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Fixpoint eval (a : exp) : state_comp nat :=
  match a with
  | ANum n       => pure n
  | AId x        => fetch x                                
  | <{a1 + a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; pure (n1 + n2)
  | <{a1 == a2}> => n1 <- eval a1 ;; n2 <- eval a2 ;; match (beq_nat n1 n2) with 
                                                                          | true     => pure 0
                                                                          | false    => pure 1
                                                                          end end.

Fixpoint exec (c : com) : state_comp unit :=
  match c with
  | <{ skip }>                    => pure tt
  | <{ x := a }>                  => n <- eval a ;; assign x n 
  | <{c1; c2}>                    => x <- exec c1 ;; y <- exec c2 ;; pure tt
  | <{if a then c1 else c2 end}>  => n <- eval a ;;
                                    match n with 
                                      | 0 => exec c1
                                      | _ => exec c2 
                                    end
  end.


