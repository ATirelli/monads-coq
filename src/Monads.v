(** * Monads in FP through examples 

The aim of this notebook is to present the use of monads in functional programming. This will be done 
mainly through examples, using three relevant use cases, in which the use of monads offers an elegant 
and unifying perspective on seemingly different problems. To highlight the relevance of the monads approach, 
for each of the use cases presented, we shall compare such an approach to the sandard _ad hoc_ solution for
the problem at hand.  *)

Require Import NPeano Arith Bool String List.
Require Import Coq.Logic.FunctionalExtensionality.

Set Implicit Arguments.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Class Show(A:Type) := {
  show : A -> string
}.

Definition digit2string(d:nat) : string := 
  match d with 
    | 0 => "0" | 1 => "1" | 2 => "2" | 3 => "3"
    | 4 => "4" | 5 => "5" | 6 => "6" | 7 => "7"
    | 8 => "8" | _ => "9"
  end %string.
  
Fixpoint digits'(fuel n:nat) (accum : string) : string := 
  match fuel with 
    | 0 => accum
    | S fuel' => 
      match n with 
        | 0 => accum
        | _ => let d := digit2string(n mod 10) in 
               digits' fuel' (n / 10) (d ++ accum)
      end
  end.

Definition digits (n:nat) : string := 
  match digits' n n "" with 
    | "" => "0"
    | ds => ds
  end %string.
  
Instance natShow : Show nat := { 
  show := digits
}.

(** We start by defining an ultra simple language of terms, 
where we have constants and divisions. This will be our toy model 
on which we will defined three monads: 
- the exception monad
- the simplified state monad
- the output monad *)

Inductive tm := 
| Con : nat -> tm
| Div : tm -> tm -> tm.

(** Following Wadler's paper, we fix our two favourite examples of terms *)

Example answer: tm := (Div (Div (Con 1972 ) (Con 2 )) (Con 23 )).
Example error: tm := (Div (Con 1)(Con 0)).

(** * The monad [Type Class] *)

(** Now we have to implement the concept of monad, and we do that using a [Type Class]. 
As we said earlier, a monad is not just a _functor_ but has additional properties. 
In the following definition,
-  [ret] is to be thought of as a way to turn 
  a value into the computation that returns that value and does nothing else
- [bind] tells us how to apply a function of type [a -> M b] to a computation of type [M a].

Following Wadler, _a monad is a triple (M,ret,bind) consisting of a type constructor M 
and two operations of the given polymorphic types_. Note that all the monads below a simplified 
reimplementations of the more refined instances of the [ext-lib] Coq library, 
 https://github.com/coq-community/coq-ext-lib. *)

Class Monad(M:Type -> Type) := 
{
  ret : forall {A:Type}, A -> M A ; 
  bind : forall {A B:Type}, M A -> (A -> M B) -> M B; 
}.


Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).

Class MonadLeft (M : Type -> Type) {H : Monad M} := 
  {
  left_id_monad : forall {A B:Type} (x:A) (f:A -> M B), bind (ret x) f = f x
  }.

Class MonadRight (M : Type -> Type) {H : Monad M} := 
  {
  right_id_monad : forall {A B:Type} (c:M A), bind c ret = c                                                       }.

Class MonadAssoc (M : Type -> Type) {H : Monad M} := 
  {
 assoc_monad : forall {A B C} (c:M A) (f:A->M B) (g:B -> M C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g)                                                      
}.

(* Not sure what this does*)
Class MonadLaws (M : Type -> Type) {H : Monad M} :=
  { M_Left :> MonadLeft;
    M_Right :> MonadRight;
    M_Assoc :> MonadAssoc}.


(** * The exception monad *)

(**  We are ready to see our first example of monad: the exception monad. Since we are
performing division between natural numbers we want to make sure that we never divide by zero and 
that whenever [0] is at the denominator of a fraction, we raise an exception. *)

Inductive Exn(A:Type) : Type := 
| Result : A -> Exn A
| Fail : string -> Exn A.
Arguments Result {A}.
Arguments Fail {A}.

(** For now, [Exn] is just a "function" that takes a type and produces an exception of that type. 
To turn it into a monad we need to provide a definition of the [ret] and [bind] functions. *)
Require Import Program.Tactics.
Instance ExnMonad : Monad Exn := 
{
  ret := fun {A:Type} (x:A) => Result x ; 
  bind := fun {A B:Type} (x:Exn A) (f:A -> Exn B) =>
            match x with 
              | Result y => f y
              | Fail s => Fail s
            end
}.


(** But, theoretically speaking, providing a definition of the [ret] and [bind] functions is not 
enough to claim that [ExnMonad] is indeed a monad. We need to prove that [ret] and [bind] satisfy
the properties for a functor to be a monad: namely, unitarity and associativity. *)

Lemma m_left_id_exn_monad : forall {A B:Type} (x:A) (f:A -> Exn B), bind (ret x) f = f x .
Proof. intros. simpl. trivial. Qed. 

Lemma m_right_id_exn_monad : forall {A B:Type} (c:Exn A), bind c ret = c. 
Proof. intros. simpl. destruct c; trivial. Qed.

Lemma m_assoc_exn_monad : forall {A B C} (c:Exn A) (f:A->Exn B) (g:B -> Exn C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g).
Proof. intros. simpl. destruct c; try destruct (f a); try trivial. Qed. 

(** We now exploit the power of [ExnMonad] and use it to write an evaluator of the 
language of terms defined above.*)

(** The type [tm -> Exn nat] indicates that the evaluator takes a term and performs a computation 
yielding a natural number. To compute [Con n], just return [n]. To compute [Div t1 t2], 
first compute [t1], bind [n1] to the result, then compute [t2], bind [n2] to the result and verify
whether the division can be performed.*)

Fixpoint eval_exn (t:tm) : Exn nat := 
  match t with 
    | Con n => ret n
    | Div t1 t2 => n1 <- eval_exn t1 ;; 
                   n2 <- eval_exn t2 ;;
                     match n2 with
                       | 0 => Fail "division by zero!"
                       | _ => ret (n1 / n2) end end.
                     
  
Compute eval_exn(answer).
(* = Result 42
     : Exn nat *)
Compute eval_exn(error).
(* = Fail "division by zero!"
     : Exn nat *)

(** It is possible to implement an evalutator handling exception _without_ the use of the Exception Monad. 
This is done as follows: *)

Fixpoint eval_exn_no_monad (t:tm) : Exn nat := 
  match t with 
    | Con n => Result n
    | Div t1 t2 => match eval_exn_no_monad t1 with 
                      | Fail s    => Fail s
                      | Result n1 => match eval_exn_no_monad t2 with 
                                                  | Fail s    => Fail s
                                                  | Result n2 => match n2 with 
                                                                  | 0 => Fail "division by zero!"
                                                                  | _ => Result (n1/n2) end end end end.

Compute eval_exn_no_monad(answer).
(* = Result 42
     : Exn nat *)
Compute eval_exn_no_monad(error).
(* = Fail "division by zero!"
     : Exn nat *)

Theorem eval_exn_equiv: forall t, eval_exn t = eval_exn_no_monad t.
Proof. intros. induction t. 
- auto.
- simpl. rewrite IHt1. rewrite IHt2. auto. Qed. 

(** * The (simple) state monad *)

Module simple_monad_state.

(** In the state monad, a computation accepts 
an initial state and returns a value paired with the final state. *)
 
Definition state:=nat.
Definition state_comp(A:Type) := state -> (state*A).

Instance StateMonad : Monad state_comp := {
  ret := fun {A:Type} (x:A) => (fun (s:state) => (s,x)) ; 
  bind := fun {A B:Type} (c : state_comp A) (f: A -> state_comp B) => 
            fun (s:state) => 
              let (s',v) := c s in 
              f v s'
}.

(** As well as for the exception monad, we need to prove that [StateMonad] satisfy 
the three relevant properties below. Note that in the proofs, we had to make use of the 
functional exptensionality axiom. *)

Lemma m_left_id_state_monad : forall {A B:Type} (x:A) (f:A -> state_comp B), bind (ret x) f = f x .
Proof. intros. simpl. apply functional_extensionality. trivial. Qed. 

Lemma m_right_id_state_monad : forall {A B:Type} (c:state_comp A), bind c ret = c. 
Proof. intros. simpl. apply functional_extensionality. intros. destruct c. trivial. Qed.  

Lemma m_assoc_state_monad : forall {A B C} (c:state_comp A) (f:A->state_comp B) (g:B -> state_comp C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g).
Proof. intros. simpl. apply functional_extensionality. intros. destruct (c x). trivial. Qed.


Fixpoint eval_state (t:tm) : state_comp nat  := 
  match t with 
  | Con n => ret n
  | Div t1 t2  => 
      n1 <- eval_state t1 ;; 
      n2 <- eval_state t2 ;; 
      fun (s:state) => ( s+1 , n1 / n2 )
      end.

Compute eval_state answer 0.

(* = (2, 42)
     : state * nat *)
Compute eval_state error 0.

(*  = (1, 0)
     : state * nat
*)

(** The follwing is an an alternative implementation of [eval_state] that does not make use of the StateMonad. *)

Fixpoint eval_state_no_monad (t:tm) : state_comp nat  := 
  match t with 
  | Con n => fun s => (s, n)
  | Div t1 t2  => fun s => let (s', n1):= eval_state_no_monad t1 s in 
                              let (s'', n2):= eval_state_no_monad t2 s' in (s''+ 1, n1/n2 ) end.

Compute eval_state_no_monad answer 0.

(* = (2, 42)
     : state * nat *)
Compute eval_state_no_monad error 0.

(*  = (1, 0)
     : state * nat
*)

Theorem eval_state_equiv: forall t, eval_state t = eval_state_no_monad t.
Proof. intros. induction t. 
- auto.
- simpl. rewrite IHt1. rewrite IHt2. apply functional_extensionality. intros. 
destruct (eval_state_no_monad t1). destruct (eval_state_no_monad t2). auto. Qed.

(** We shall come back to the state monad, when dealing with a slightly more complicated language, 
a simplified version of [IMP], where we shall use a more refined definition of state. *)

End simple_monad_state.

(** * The output monad*)


Instance expShow : Show tm := {
  show := fix show_exp (t:tm) : string := 
              match t with 
                | Con n => "(Con "++ show n ++")"
                | Div t1 t2 => "(Div " ++ (show_exp t1) ++ (show_exp t2) ++ ")"
              end %string
}.

Definition output_comp(A:Type):Type := string*A.

(** In the output monad, a computation consists of the output generated paired 
with the value returned.

The call [ret] a returns no output paired with [x]. 
In the [bind] we extracts output [s] and value [x] from computation [c], 
then we extract output [t] and value [y] from computation [f(x)],
and return the output formed by concatenating [s] and [s] paired with the value [y].*)

Instance OutputMonad : Monad output_comp := {
  ret := fun {A:Type} (x:A) => (""%string,x) ; 
  bind := fun {A B:Type} (c : output_comp A) (f: A -> output_comp B) => 
           let (s, x):= c in
           let (t, y):= f x in 
           (append s t, y)
}.


(** As usual, we have to prove that what we have just defined is indeed a monad. *)

Lemma m_left_id_out_monad : forall {A B:Type} (x:A) (f:A -> output_comp B), bind (ret x) f = f x.
Proof. intros. simpl. destruct (f x). reflexivity. Qed.

Lemma app_empty_str: forall (s:string), (s ++ "")%string = s.
Proof. induction s. - simpl. reflexivity.
                    - simpl. rewrite -> IHs. trivial. Qed.
                    
Lemma m_right_id_out_monad : forall {A B:Type} (c:output_comp A), bind c ret = c. 
Proof. intros. simpl. destruct c.  rewrite app_empty_str. reflexivity. Qed.

Lemma app_assoc_string: forall (s s1 s2: string), append (append s s1) s2 = append s (append s1 s2).
Proof. intros s s1. induction s.
- intros. simpl. reflexivity.
- intros. simpl. rewrite IHs. reflexivity. Qed.
 
Lemma m_assoc_out_monad : forall {A B C} (c:output_comp A) (f:A->output_comp B) (g:B -> output_comp C), 
    bind (bind c f) g = bind c (fun x => bind (f x) g).
Proof. intros. simpl. destruct c. destruct (f a). destruct (g b). rewrite app_assoc_string. reflexivity. Qed.


Definition line(t:tm) (n:nat):string:=
(append (append "eval"%string (show (t))) (append "<="%string (append (show n ) "
      "%string))).


(** Using the [OutputMonad] we can modify our evaluator so that, for a given computation to perform, 
we collect all the intermediate steps and print them at the end of the computation. The function [line] 
 used in the definition below is only used for pretty printing. *)

Fixpoint eval_output (t:tm) : output_comp nat  := 
  match t with 
  | Con n =>   (line (Con n) n, n)
  | Div t1 t2  => 
      n1 <- eval_output t1 ;; 
      n2 <- eval_output t2 ;; 
      (line (Div t1 t2) (n1/n2), n1/n2 ) end.

Compute eval_output answer . 

(* = = ("eval(Con 1972)<=1972
      eval(Con 2)<=2
      eval(Div (Con 1972)(Con 2))<=986
      eval(Con 23)<=23
      eval(Div (Div (Con 1972)(Con 2))(Con 23))<=42
      "%string,
       42)
     : output_comp nat *)

(** Note that, to get the output in the reverse order, all 
that is required is to change the definition of [bind], replacing [append s t] by [append t s]. 
This is commensurate with the change 
required in the pure program, and rather simpler than the change required in an impure program.*)

(** As for the two cases above, we present a solution of the problem of defining the output evaluator that does
not make use of the Output Monad. *)

Fixpoint eval_output_no_monad (t:tm) : output_comp nat  := 
  match t with 
  | Con n =>   (line (Con n) n, n)
  | Div t1 t2  => let (s1, n1):= eval_output_no_monad t1 in 
                      let (s2, n2):= eval_output_no_monad t2 in
                              (append s1 (append s2 (line (Div t1 t2) (n1/n2))), n1/n2) end.

Theorem eval_output_equiv: forall t, eval_output t = eval_output_no_monad t.
Proof. intros. induction t. 
- auto.
- simpl. rewrite IHt1. rewrite IHt2. 
destruct (eval_output_no_monad t1). destruct (eval_output_no_monad t2). auto. Qed.

Compute eval_output_no_monad answer .
