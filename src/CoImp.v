Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import FunctionalExtensionality.
Import ListNotations.
Require Import Monads.Delay.
Require Import Monads.Computation.


(** * IMP *)

(** We now turn our attention to _IMP_, a simple - yet Turing complete - 
imperative language, where we can compute simple arithmetic expressions, 
assign vaalues to variable and perform _potentially non terminating_ loops
through the [While] constructor. *)

(*Maps*)
Definition total_map (A : Type) := string -> A.

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).
Definition state := total_map nat.

(*IMP*)
Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)            
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).


Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

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
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.



Definition empty_st := (_ !-> 0).


Notation "x '!->' v" := (t_update empty_st x v) (at level 100).
Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).


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
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

(** As we all know, we can define define the relational version BSOS for IMP 
as follows. One disadvantage of this approach is that it considers only _terminating_
programs, i.e. there cannot no proposition of the form [ceval P st1 st2] is provable 
if [P] is a non terminating program. *)

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
   
(** One possibility to _partially_ evaluate general IMP programs using the standard 
_gas_ construction below, where the BSOS function takes as a further argument a [nat] i 
which is the number of reduction steps we allow. Note that for any non-terminating program 
the output of [ceval_step] will be [None] regardless of the gas parameter. *)

Fixpoint ceval_step (st : state) (c : com) (i : nat) {struct i}
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | <{ skip }> =>
          Some st
      | <{ l := a1 }> =>
          Some (t_update st l (aeval st a1))
      | <{ c1 ; c2 }> =>
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | <{ if b then c1 else c2 end }> =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | <{ while b1 do c1 end }> =>
          if (beval st b1)
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 2 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.

(** * IMP BSOS with [Computation]*)
(** Using [Computation] we can write a total _function_ that computes the BSOS 
of any IMP program, regardless of whether the program terminates or not *)

CoFixpoint ceval_comp (st : state) (c : com) : Computation state :=
match c with
      | <{ skip }> =>
          Return st
      | <{ l := a1 }> =>
          Return (t_update st l (aeval st a1))
      | <{ c1 ; c2 }> =>
          st' <- ceval_comp st c1 ; ceval_comp st' c2
      | <{ if b then c1 else c2 end }> =>
           v <- Return (beval st b); match v with 
                                        | true  => ceval_comp st c1
                                        | false => ceval_comp st c2 end

      | <{ while b1 do c' end }> =>
          v <- Return (beval st b1); match v with 
                                        | true  => st' <- ceval_comp st c'; Step (ceval_comp st' c)
                                        | false => Return st end
          
end.


Definition Loop:= <{while true do skip end}>. 
Definition NonTrivialLoop:= <{while 0<=X do X:=X+1 end}>. 

CoFixpoint Never:= @Step (state) Never.
CoFixpoint never:= @step (state) never.

Definition P:= <{X:=0; while X=0 do X:=X + 1 end }>.
Definition stP:= X !-> 1.

Lemma Return_interp_rtrn: forall {A} (x:A), (interp (Return x)) = rtrn x.
Proof. intros. eval_ ((interp (Return x))). reflexivity. Qed.

  Theorem P_evals_to_stP: Eqp (interp (ceval_comp empty_st P)) (rtrn stP).
  Proof. 
  eval_ (interp (ceval_comp empty_st P)).
  eval_ (interp (ceval_comp (X !-> 0) <{ while X = 0 do X := X + 1 end }>)). 
  eval_ (interp
  (st' <- ceval_comp (X !-> 0) <{ X := X + 1 }>;
   Step (ceval_comp st' <{ while X = 0 do X := X + 1 end }>))).
    apply eqp_value with (a:= stP).
  -   
  eval_ (interp
  (Step
     (ceval_comp (t_update (X !-> 0) X 1)
        <{ while X = 0 do X := X + 1 end }>))). 
  eval_ ((interp
  (ceval_comp (t_update (X !-> 0) X 1)
     <{ while X = 0 do X := X + 1 end }>))).
      repeat constructor. assert ((t_update (X !-> 0) X 1)= stP). 
    apply functional_extensionality; intros; unfold stP; unfold t_update; 
  destruct (eqb_string X x); reflexivity.
    rewrite H. rewrite Return_interp_rtrn. apply value_return with (a:=stP).
  - constructor. Qed.  

Theorem Loop_is_Never: forall st, Eqp (interp (ceval_comp st Loop)) never.
Proof. 
intros. cofix CIH. eval_ (interp (ceval_comp st Loop)).
eval_ (interp (st' <- ceval_comp st <{ skip }>; Step (ceval_comp st' Loop))).
eval_ ((interp (Step (ceval_comp st Loop)))).
eval_ (never). eval_ (never). eval_ (never). repeat constructor. apply CIH. Qed.  
    

Theorem Loop_is_NonTrivialLoop: 
forall st1 st2, Eqp (interp (ceval_comp st1 Loop)) (interp (ceval_comp st2 NonTrivialLoop)). 
Proof. 
cofix CIH. intros.
eval_ (interp (ceval_comp st1 Loop)).
eval_ (interp (st' <- ceval_comp st1 <{ skip }>; Step (ceval_comp st' Loop))).
eval_ (interp (Step (ceval_comp st1 Loop))).
eval_ (interp (ceval_comp st2 NonTrivialLoop)).
eval_ (interp
(st' <- ceval_comp st2 <{ X := X + 1 }>;
 Step (ceval_comp st' NonTrivialLoop))).
eval_ (interp
(Step (ceval_comp (t_update st2 X (st2 X + 1)) NonTrivialLoop))).
repeat constructor. apply CIH. Qed.

(** Why did we use [Computation] instead of [Partial]? Because [bind] is a 
_function_ and _not_ a _constructor_ and therefore the definition that we would use 
would not comply with the syntactic criterion required by the termination checker. *)

Fail CoFixpoint ceval_partial (st : state) (c : com) : Partial state :=
match c with
      | <{ skip }> =>
          rtrn st
      | <{ l := a1 }> =>
          rtrn (t_update st l (aeval st a1)) 
      | <{ c1 ; c2 }> =>
          st' <=== ceval_partial st c1 ; ceval_partial st' c2
      | <{ if b then c1 else c2 end }> =>
           v <=== rtrn (beval st b); match v with 
                                        | true  => ceval_partial st c1
                                        | false => ceval_partial st c2 end

      | <{ while b1 do c' end }> =>
          v <=== rtrn (beval st b1); match v with 
                                        | true  => st' <=== ceval_partial st c'; step (ceval_partial st' c)
                                        | false => rtrn st end
          
end.

(* Implement constant folding for expressions and commands *)

Fixpoint fold_constants_aexp (a : aexp) : aexp :=
  match a with
  | ANum n       => ANum n
  | AId x        => AId x
  | <{ a1 + a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 + n2)
    | (a1', a2') => <{ a1' + a2' }>
    end
  | <{ a1 - a2 }> =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 - n2)
    | (a1', a2') => <{ a1' - a2' }>
    end
  | <{ a1 * a2 }>  =>
    match (fold_constants_aexp a1,
           fold_constants_aexp a2)
    with
    | (ANum n1, ANum n2) => ANum (n1 * n2)
    | (a1', a2') => <{ a1' * a2' }>
    end
  end.

Example fold_aexp_ex1 :
    fold_constants_aexp <{ (1 + 2) * X }>
  = <{ 3 * X }>.
Proof. reflexivity. Qed.

(** Note that this version of constant folding doesn't do other
    "obvious" things like eliminating trivial additions (e.g.,
    rewriting [0 + X] to just [X]).: we are focusing attention on a
    single optimization for the sake of simplicity.

    It is not hard to incorporate other ways of simplifying
    expressions -- the definitions and proofs just get longer.  We'll
    consider optimizations in the exercises. *)

Example fold_aexp_ex2 :
  fold_constants_aexp <{ X - ((0 * 6) + Y) }> = <{ X - (0 + Y) }>.
Proof. reflexivity. Qed.

(** Not only can we lift [fold_constants_aexp] to [bexp]s (in the
    [BEq], [BNeq], and [BLe] cases); we can also look for constant
    _boolean_ expressions and evaluate them in-place as well. *)

Fixpoint fold_constants_bexp (b : bexp) : bexp :=
  match b with
  | <{true}>        => <{true}>
  | <{false}>       => <{false}>
  | <{ a1 = a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 =? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' = a2' }>
      end
  | <{ a1 <= a2 }>  =>
      match (fold_constants_aexp a1,
             fold_constants_aexp a2) with
      | (ANum n1, ANum n2) =>
          if n1 <=? n2 then <{true}> else <{false}>
      | (a1', a2') =>
          <{ a1' <= a2' }>
      end

  | <{ ~ b1 }>  =>
      match (fold_constants_bexp b1) with
      | <{true}> => <{false}>
      | <{false}> => <{true}>
      | b1' => <{ ~ b1' }>
      end
  | <{ b1 && b2 }>  =>
      match (fold_constants_bexp b1,
             fold_constants_bexp b2) with
      | (<{true}>, <{true}>) => <{true}>
      | (<{true}>, <{false}>) => <{false}>
      | (<{false}>, <{true}>) => <{false}>
      | (<{false}>, <{false}>) => <{false}>
      | (b1', b2') => <{ b1' && b2' }>
      end
  end.

Example fold_bexp_ex1 :
  fold_constants_bexp <{ true && ~(false && true) }>
  = <{ true }>.
Proof. reflexivity. Qed.

Example fold_bexp_ex2 :
  fold_constants_bexp <{ (X = Y) && (0 = (2 - (1 + 1))) }>
  = <{ (X = Y) && true }>.
Proof. reflexivity. Qed.

(** To fold constants in a command, we apply the appropriate folding
    functions on all embedded expressions. *)

Fixpoint fold_constants_com (c : com) : com :=
  match c with
  | <{ skip }> =>
      <{ skip }>
  | <{ x := a }> =>
      <{ x := (fold_constants_aexp a) }>
  | <{ c1 ; c2 }>  =>
      <{ fold_constants_com c1 ; fold_constants_com c2 }>
  | <{ if b then c1 else c2 end }> =>
      match fold_constants_bexp b with
      | <{true}>  => fold_constants_com c1
      | <{false}> => fold_constants_com c2
      | b' => <{ if b' then fold_constants_com c1
                       else fold_constants_com c2 end}>
      end
  | <{ while b do c1 end }> =>
      match fold_constants_bexp b with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do (fold_constants_com c1) end }>
      end
  end.

Example fold_com_ex1 :
  fold_constants_com
    (* Original program: *)
    <{ X := 4 + 5;
       Y := X - 3;
       if ((X - Y) = (2 + 4)) then skip
       else Y := 0 end;
       if (0 <= (4 - (2 + 1))) then Y := 0
       else skip end;
       while (Y = 0) do
         X := X + 1
       end }>
  = (* After constant folding: *)
    <{ X := 9;
       Y := X - 3;
       if ((X - Y) = 6) then skip
       else Y := 0 end;
       Y := 0;
       while (Y = 0) do
         X := X + 1
       end }>.
Proof. reflexivity. Qed.

  Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.
  Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
    forall (a : aexp),
      aequiv a (atrans a).
  
  Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
    forall (b : bexp),
      bequiv b (btrans b).
  
      Theorem fold_constants_aexp_sound :
      atrans_sound fold_constants_aexp.
    Proof.
      unfold atrans_sound. intros a. unfold aequiv. intros st.
      induction a; simpl;
        (* ANum and AId follow immediately *)
        try reflexivity;
        (* APlus, AMinus, and AMult follow from the IH
           and the observation that
                  aeval st (<{ a1 + a2 }>)
                = ANum ((aeval st a1) + (aeval st a2))
                = aeval st (ANum ((aeval st a1) + (aeval st a2)))
           (and similarly for AMinus/minus and AMult/mult) *)
        try (destruct (fold_constants_aexp a1);
             destruct (fold_constants_aexp a2);
             rewrite IHa1; rewrite IHa2; reflexivity). Qed.

(*Theorem CSeq_congruence : forall c1 c1' c2 c2',
             cequiv c1 c1' -> cequiv c2 c2' ->
             cequiv <{ c1;c2 }> <{ c1';c2' }>.
           Proof.
             (* FILL IN HERE *) Admitted.*)


Theorem equiv_while_true: forall b, bequiv b <{ true }> ->
  forall c st,
  Eqp (interp (ceval_comp st <{ while b do c end }>)) never.
  Proof. intros. generalize dependent st .  generalize dependent c. cofix CIH.
  intros. eval_ (interp (ceval_comp st <{ while b do c end }>)).
  assert (beval st b = true). {apply H. } rewrite H0. eval_ (never).
  constructor. 
  eval_ (interp (st' <- ceval_comp st c; Step (ceval_comp st' <{ while b do c end }>))). destruct c.
    + simpl. eval_ (interp (Step (ceval_comp st <{ while b do skip end }>))). eval_ (never).
      eval_ (never). repeat constructor. apply CIH.
    + simpl. eval_ (never). repeat constructor. 
      eval_ (interp (Step (ceval_comp (t_update st x (aeval st a)) <{ while b do x := a end }>))). 
      eval_ (never). repeat constructor. apply CIH. Admitted. 

Theorem constant_folding_com: 
forall c st, Eqp (interp (ceval_comp st c)) (interp (ceval_comp st (fold_constants_com c))).
Proof. cofix CIH. intros. destruct c.
  - simpl. eval_ (interp (ceval_comp st <{ skip }>)).
  - simpl. eval_ (interp (ceval_comp st <{ x := a }>)). 
    eval_ (interp (ceval_comp st <{ x := (fold_constants_aexp a) }>)).
    rewrite fold_constants_aexp_sound. apply eqp_refl.
  - eval_ (interp (ceval_comp st <{ c1; c2 }>)).
    eval_ (interp (ceval_comp st <{ (fold_constants_com c1); (fold_constants_com c2) }>)). simpl. 
     admit.
  - admit.
  - cofix CIH1. eval_ (interp (ceval_comp st <{ while b do c end }>)). 
    destruct b eqn: Hb.
    + simpl. eval_ (interp (ceval_comp st <{ while true do skip end }>)). constructor.  apply CIH1. 