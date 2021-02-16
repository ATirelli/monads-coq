(** * The state monad *)

Require Import NPeano Arith Bool String List.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B
}.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** We now use a more refined definition for [state]: it is no more just an integer accounting for the 
total number of computations needed to evaluate a term, but a [map] from [string] to [nat]. *)

(** [ 
]
From Wadler's paper, we read: 

_There is an important difference between the way monads are used in 
the previous section and the way monads are used here. 
The previous section showed monads help to use existing language 
features more effectively; this section shows how monads can help define new language features. 
No change to the programming language is required, but the implementation must provide a 
new abstract data type, perhaps as part of the standard prelude.
Here monads are used to manipulate state internal to the program_. *)

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

Definition empty_st := (_ !-> 0).

(** It will also be useful to consider the [type] [unit], which has the property of having only one 
inhabitant. To mimic Wadler's notation, we shall denote such an inhabitant with [()]. *)

Notation "()" := tt.

(** As for the [StateMonad] seen earlier, we define the [state_comp] function, which, given a type [A], 
constructs a new type [state_comp A], which is a map [state -> (A*state)]. *)

Definition state_comp(A:Type) := state -> (A*state).

(** The definition below is identical to the one we have already seen, but where [state] is not just a [nat]. 
A such, the statements and the corresponding proofs of the monad properties can be copied verbatim. *)

Instance StateMonad : Monad state_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => (x, s)) ; 
  bind := fun {A B:Type} (c : state_comp A) (f: A -> state_comp B) => 
            fun (s:state) => 
              let (v, s') := c s in 
              f v s'
}.

Lemma m_left_id_state_monad : forall {A B:Type} (x:A) (f:A -> state_comp B), bind (ret x) f = f x .
Proof. intros. simpl. apply functional_extensionality. trivial. Qed. 

Lemma m_right_id_state_monad : forall {A B:Type} (c:state_comp A), bind c ret = c. 
Proof. intros. simpl. apply functional_extensionality. intros. destruct c. trivial. Qed.  

Lemma m_assoc_state_monad : forall {A B C} (c:state_comp A) (f:A->state_comp B) (g:B -> state_comp C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g).
Proof. intros. simpl. apply functional_extensionality. intros. destruct (c x). trivial. Qed.



(** 
You might argue that building all this for the simple term language we have used to far as running
example is an overkill and might not even make sense. You are right: we something a bit more sophisticated. 
For this purpose, we are going to use a simplified version of [IMP], the simple imperative language we have 
been working on in the _Formal Methods_ course. We want to complicate things, but not too much: we therefore 
limit ourselves to considering expression which are: 
- natural numbers 
- variable IDs
- sum of expressions 
- equations between expressions. *)

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

(** We now need two functions that allow us to interact with states: 
- the function [block]: the call [block n m] creates a new state with all locations initialised to [n],
 applies monad [m] to this initial state to yield value [a] and final state [x], deallocates the array, and returns [a].
- the function [fetch]: the call [fetch x] returns the value at index [x] (indices in our case are just strings)
 in the current state, and leaves the state unchanged.
- the function [assign]: the call [assign x n] returns the empty value [()],
 and updates the state so that index [x] contains value [n].*)

Definition block{A:Type} (n:nat) (m: state_comp A): A :=
let (a,_):= m (newarray n) in a.

Definition fetch (x:string) : state_comp nat := 
  fun s => (s x, s).

Definition assign (x:string) (n:nat) : state_comp unit := 
  fun s => ((), state_update s x n).

(** In contrast with the previous section, in the code below, we first present implementations of [eval] and 
[exec] that do not make use of the concept of monad, as they might the easier to read, especially if one
keeps in mind the how we have defined small/big step semantics for IMP. *)

Fixpoint eval_no_monad (a : exp)(s: state): nat :=
  match a with
  | ANum n       => n
  | AId x        => s x                                
  | <{a1 + a2}>  => (eval_no_monad a1 s) + (eval_no_monad a2 s)
  | <{a1 == a2}> => let n1 := eval_no_monad a1 s in 
                            let n2:= eval_no_monad a2 s in if (beq_nat n1 n2) then 0 else 1 end.

Fixpoint exec_no_monad (c : com)(s: state) : state :=
  match c with
  | <{ skip }>                    => s
  | <{ x := a }>                  => let n:= eval_no_monad a s in state_update s x n
  | <{c1; c2}>                    => exec_no_monad c2 (exec_no_monad c1 s)
  | <{if a then c1 else c2 end}>  => let n:= eval_no_monad a s in
                                                      match n with 
                                                        | 0 => exec_no_monad c1 s
                                                        | _ => exec_no_monad c2 s
                                                      end
  end.

Compute eval_no_monad <{Z + 1}> empty_st.

Definition fact_in_coq : com :=
  <{ Z := X;
     Y := 1;
     if Z == 0 then
       Y := Y + Z
      else
       Z := Z + 1
     end
     }>.

Compute exec_no_monad fact_in_coq empty_st X.
Compute exec_no_monad fact_in_coq empty_st Y.

(** Let us now define [eval] and [exec] using the State Monad. We first evaluate expressions: evaluation of a term 
returns a [nat] and may access or modify the state.
In fact, evaluation only accesses the state and never alters it. The intepretation, e.g. in the case of 
addition, goes as follows: [eval (<{a1 + a2}>)] tells you to compute the evaluation of [a1],
bind [n1] to the result, then compute the evaluation of [a2], bind [n1] to the result, then return [n1 + n2]. 
*)

Fixpoint eval (a : exp) : state_comp nat :=
  match a with
  | ANum n       => ret n
  | AId x        => fetch x                                
  | <{a1 + a2}>  => n1 <- eval a1 ;; n2 <- eval a2 ;; ret (n1 + n2)
  | <{a1 == a2}> => n1 <- eval a1 ;; n2 <- eval a2 ;; if (beq_nat n1 n2) then ret 0 else ret 1 end.


(** We now define execution on commands: note that, as opposed to [eval],
execution of a command returns nothing and may access or modify the state. How do we interpret the code 
below? In the case of a sequence of commands, we have that [exec <{c1; c2}>] tells you to 
compute the execution of [c1], then compute the execution of [c2], then return nothing. *)

Fixpoint exec (c : com) : state_comp unit :=
  match c with
  | <{ skip }>                    => ret ()
  | <{ x := a }>                  => n <- eval a ;; assign x n 
  | <{c1; c2}>                    => x <- exec c1 ;; y <- exec c2 ;; ret ()
  | <{if a then c1 else c2 end}>  => n <- eval a ;;
                                    match n with 
                                      | 0 => exec c1
                                      | _ => exec c2 
                                    end
  end.


Compute snd (exec fact_in_coq empty_st) X.
Compute snd (exec fact_in_coq empty_st) Y.

(**  As a final step, we prove that [eval] is equivalent to [eval_no_monad] and that 
[exec] is equivalent to [exec_no_monad]. *)

Lemma eval_not_mod_state: forall a s, snd (eval a s) = s.
Proof. intros. induction a; try auto; 
simpl; destruct (eval a1 s); unfold snd in IHa1; rewrite IHa1; 
destruct (eval a2 s); unfold snd in *; try destruct (n =? n0); assumption.
Qed.

Theorem eval_equiv: forall e s, eval_no_monad e s = fst (eval e s).
Proof. intros. induction e; try auto.
- simpl. rewrite IHe1. rewrite IHe2.  remember (eval e1 s). 
apply (f_equal snd) in Heqp. rewrite eval_not_mod_state in Heqp. apply eq_sym in Heqp.
 destruct (eval e1 s).   rewrite Heqp. subst. destruct p. unfold snd. destruct (eval e2 s). auto.
- simpl. rewrite IHe1. rewrite IHe2.  remember (eval e1 s). 
apply (f_equal snd) in Heqp. rewrite eval_not_mod_state in Heqp. apply eq_sym in Heqp.
destruct (eval e1 s).   rewrite Heqp. subst. destruct p. unfold snd. destruct (eval e2 s). 
unfold fst.
destruct (fst (n0, s) =? fst (n1, s1)); destruct (n0 =? n1); auto. Qed.

Theorem exec_equiv: forall c s, exec_no_monad c s = snd (exec c s).
Proof. intros. generalize dependent s. induction c; try auto.

- intros. simpl. rewrite eval_equiv.  remember (eval a s). apply (f_equal snd) in Heqp.
rewrite eval_not_mod_state in Heqp. destruct (eval a s). destruct p. unfold snd in Heqp.
subst.  unfold fst. unfold assign. unfold snd. auto.

- intros. simpl. rewrite IHc1.  rewrite IHc2. remember (exec c1 s).
destruct p. unfold snd.  destruct (exec c2 s0). auto. 

- intros. simpl.  rewrite eval_equiv. rewrite IHc1.  rewrite IHc2. 
remember (eval a s). apply (f_equal snd) in Heqp. rewrite eval_not_mod_state in Heqp. 
destruct p. unfold snd in Heqp. subst. unfold fst. destruct n; auto. Qed.


(**  From Wadler we read: _How a functional language may provide in-place array update is an old problem. 
This section has presented a new solution, consisting of two abstract data types with eight operations between them. 
No change to the programming language is required, other than to provide an implementation of these types, 
perhaps as part of the standard prelude. The discovery of such a simple solution comes as a surpise, 
considering the plethora of more elaborate solutions that have been proposed_. *)



