(** * The Imp language  *)

(** We now demonstrate how to use ITrees in the context of verified compilation.
    To this end, we will consider a simple compiler from an imperative language
    to a control-flow-graph language.  The meaning of both languages will be
    given in terms of ITrees, so that the proof of correctness is expressed by
    proving a bisimulation between ITrees.

    We shall emphasize two main satisfying aspects of the resulting
    formalization.

    - Despite the correctness being termination-sensitive, we do not write any
      cofixpoints. All reasoning is purely equational, and the underlying
      coinductive reasoning is hidden on the library side.

    - We split the correctness in two steps. First, a linking theory of the CFG
      language is proved correct. Then, this theory is leveraged to prove the
      functional correctness of the compiler. The first piece is fairly generic,
      and hence reusable.
 *)

(** This tutorial is composed of the following files:
    - Utils_tutorial.v     : Utilities
    - Fin.v                : Finite types as a categorical embedding
    - KTreeFin.v           : Subcategory of ktrees over finite types
    - Imp.v                : Imp language, syntax and semantics
    - Asm.v                : Asm language, syntax and semantics
    - AsmCombinators.v     : Linking theory for Asm
    - Imp2Asm.v            : Compiler from Imp to Asm
    - Imp2AsmCorrectness.v : Proof of correctness of the compiler
    - AsmOptimizations.v   : (Optional) optimization passes for the Asm language
    The intended entry point for reading is Imp.v.
 *)

(** We start by introducing a simplified variant of Software
    Foundations' [Imp] language.  The language's semantics is first expressed in
    terms of [itree]s.  The semantics of the program can then be obtained by
    interpreting the events contained in the trees.
*)

(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.Writer
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.
(* end hide *)

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

(** For simplicity, the language manipulates [nat]s as values. *)
Definition value : Type := nat.

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : value)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr).



(** Implement constant folding at the statememnt level *)

(** The statements are straightforward. The [While] statement is the only
 potentially diverging one. *)

Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Output (str : string)              (* output e *)
| Skip                           (* ; *)
.

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: nat -> expr := Lit.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: nat >-> expr.

  Declare Scope expr_scope.
  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Declare Scope stmt_scope.
  Bind Scope stmt_scope with stmt.

  Notation "x '←' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a ';;;' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';;;' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'IF' i 'THEN' t 'ELSE' e 'FI'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'IF'  i '/' '[' 'THEN'  t  ']' '/' '[' 'ELSE'  e ']' 'FI' ']'").

  Notation "'WHILE' t 'DO' b" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v  ' 'WHILE'  t  'DO' '/' '[v' b  ']' ']'").

    Notation "'OUTPUT' e" :=
    (Output e)
      (at level 100,
       right associativity,
       format
         "'[v  ' 'OUTPUT'  e ']'").

End ImpNotations.

Import ImpNotations.

(* ========================================================================== *)
(** ** Semantics *)

(** _Imp_ produces effects by manipulating its variables.  To account for this,
    we define a type of _external interactions_ [ImpState] modeling reads and
    writes to global variables.

    A read, [GetVar], takes a variable as an argument and expects the
    environment to answer with a value, hence defining an event of type
    [ImpState value].

    Similarly, [SetVar] is a write event parameterized by both a variable and a
    value to be written, and defines an event of type [ImpState unit], no
    informative answer being expected from the environment.  *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState value
| SetVar (x : var) (v : value) : ImpState unit.

(** We can now define the denotation of _Imp_ expressions and statements.  We
    parameterize the denotation by a universe of events [eff], of which
    [ImpState] is assumed to be a subevent.  *)

(** We can now define the denotation of _Imp_ expressions and statements.  We
    parameterize the denotation by a universe of events [eff], of which
    [ImpState] is assumed to be a subevent.  *)


Section Denote.

  (** We now proceed to denote _Imp_ expressions and statements.
      We could simply fix in stone the universe of events to be considered,
      taking as a semantic domain for _Imp_ [itree ImpState X]. That would be
      sufficient to give meaning to _Imp_, but would prohibit us from relating this
      meaning to [itree]s stemmed from other entities. Therefore, we
      parameterize the denotation of _Imp_ by a larger universe of events [eff],
      of which [ImpState] is assumed to be a subevent. *)

  (** _Imp_ expressions are denoted as [itree eff value], where the returned
      value in the tree is the value computed by the expression.
      In the [Var] case, the [trigger] operator smoothly lifts a single event to
      an [itree] by performing the corresponding [Vis] event and returning the
      environment's answer immediately.
      A constant (literal) is simply returned.
      Usual monadic notations are used in the other cases: we can [bind]
      recursive computations in the case of operators as one would expect. *)
Fixpoint denote_expr (e : expr) : itree (ImpState +' (writerE string)) value :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l + r)
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; ret (l - r)
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; ret (l * r)
    end.

  

  Definition while (step : itree (ImpState +' (writerE string)) (unit + unit)) : 
    itree (ImpState +' (writerE string)) unit :=
    iter (C := Kleisli _) (fun _ => step) tt.

  (** Casting values into [bool]:  [0] corresponds to [false] and any nonzero
      value corresponds to [true].  *)
  Definition is_true (v : value) : bool := if (v =? 0)%nat then false else true.

  (** The meaning of Imp statements is now easy to define.  They are all
      straightforward, except for [While], which uses our new [while] combinator
      over the computation that evaluates the conditional, and then the body if
      the former was true.  *)
  Fixpoint denote_imp (s : stmt) : itree (ImpState +' (writerE string)) unit :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v)
    | Seq a b    =>  denote_imp a ;; denote_imp b
    | If i t e   =>
      v <- denote_expr i ;;
      if is_true v then denote_imp t else denote_imp e

    | While t b =>
      while (v <- denote_expr t ;;
	           if is_true v
             then denote_imp b ;; ret (inl tt)
             else ret (inr tt))
    | Output str =>  tell str
    | Skip => ret tt
    end.



From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Data.String
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
     Definition env := alist var value.


Definition empty : env := nil.

Definition handle_ImpState: ImpState ~> itree (mapE var 0) :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x
    | SetVar x v => insert x v
    end.

    Typeclasses eauto := 5.
    Example while_different_print_not_equivalent: 
    (denote_imp (While (Lit 1) (Output "s")) ≈ 
    denote_imp (While (Lit 1) (Output "n"))) -> False.
  Proof.
    Admitted. 

End Denote.
Check denote_imp. 

Definition interp_imp_implicit_E {E} (t : itree (ImpState +' E) unit) :
  stateT (env) (itree E) unit :=
   interp_map (interp (bimap handle_ImpState (id_ E)) t).

Definition interp_imp_state:= @interp_imp_implicit_E (writerE string).
Check interp_imp_state.

Definition eval_imp_state (s: stmt) : itree (writerE string) (env * unit) :=
  interp_imp_state (denote_imp s) empty.

Variant voidE : Type -> Type :=  .

Check interp (@handle_writer_list string voidE) .

Definition interp_output (t : itree (writerE string) (env * unit)) :=
  interp (@handle_writer_list string voidE) t.

Definition eval_imp (s: stmt)  :=
  interp_output (interp_imp_state (denote_imp s) empty) nil.

Section Example_Fact.
Open Scope expr_scope.
Open Scope stmt_scope.
Variable input: var.
Variable output: var.

Definition fact (n:nat): stmt :=
  input ← n;;;
  output ← 1;;;
  WHILE input
  DO output ← output * input;;;
    Output "some statement";;;
     input  ← input - 1.
End Example_Fact.

Compute (burn 2000 (eval_imp (fact "input" "output" 9))).


Global Instance eutt_interp_imp_state:
Proper (@eutt (ImpState +' (writerE string)) unit unit eq ==> eq ==> @eutt (writerE string) (prod (env) unit) (prod _ unit) eq)
  interp_imp_state.
Proof.
  repeat intro.
  subst.
  unfold interp_imp_state.
  unfold interp_imp_implicit_E.
  unfold interp_map. rewrite H. reflexivity. Qed.
  
Check @eutt (writerE string) (prod (env) unit) (prod _ unit) .
Check interp_imp_state.
Global Instance eutt_interp_output:
  Proper (@eutt (writerE string) (env * unit) (env * unit) eq ==>
          eq ==>
          @eutt voidE (prod (list string) (env * unit)) (prod _ (env * unit)) eq)
  interp_output.
Proof.
  repeat intro.
  subst.
  unfold interp_output.
  rewrite H. reflexivity. Qed.


Fixpoint fold_constants_expr (a : expr) : expr :=
          match a with
          | Var x => Var x
          | Lit n => Lit n
          | Plus a1 a2 =>
            match (fold_constants_expr a1,
                   fold_constants_expr a2)
            with
            | (Lit n1, Lit n2) => Lit (n1 + n2)
            | (a1', a2') => Plus a1' a2'
            end
          | Minus a1 a2 =>
            match (fold_constants_expr a1,
                   fold_constants_expr a2)
            with
            | (Lit n1, Lit n2) => Lit (n1 - n2)
            | (a1', a2') => Minus a1' a2'
            end
          | Mult a1 a2 =>
            match (fold_constants_expr a1,
                   fold_constants_expr a2)
            with
            | (Lit n1, Lit n2) => Lit (n1 * n2)
            | (a1', a2') => Mult a1' a2'
            end
          end.
        
          Fixpoint fold_constants_stmt (s : stmt) : stmt :=
            match s with
            | Assign x e => Assign x (fold_constants_expr e)
            | Seq s1 s2 => Seq (fold_constants_stmt s1) (fold_constants_stmt s2)
            | If e s1 s2 => match fold_constants_expr e with
                            | Lit 0 => fold_constants_stmt s2
                            | Lit _ => fold_constants_stmt s1
                            | e' => If e' (fold_constants_stmt s1) (fold_constants_stmt s2)
                            end
            | While e s => match fold_constants_expr e with
                           | Lit 0 => Skip
                           | Lit (S x) => While (Lit (S x)) (fold_constants_stmt s)
                           | e' => While e' (fold_constants_stmt s)
                           end
            | Output e => Output e
            | Skip => Skip
            end.
          
Theorem denote_imp_fold_constants_expr : forall e,
              denote_expr  (fold_constants_expr e) ≅ denote_expr e.
Proof.
            intros e; induction e; try reflexivity.
            all: cbn; setoid_rewrite <- IHe1; setoid_rewrite <- IHe2.
            all: destruct (fold_constants_expr e1) eqn:Eq1, (fold_constants_expr e2) eqn:Eq2.
            all: cbn; try reflexivity.
            all: now rewrite ?bind_ret_l.
          Qed.
          
          Ltac bind := eapply eq_itree_clo_bind; [reflexivity | intros ? ? <-].
          
          (* This is what tripped me: without this instance, the rewrite marked as "HERE" in the proof below fails, forcing you to work around awkwardly otherwise *)
          #[global] Instance missing_iter_instance {E R I}:
            Proper (pointwise_relation I (eq_itree eq) ==> eq ==> eq_itree eq) (@ITree.iter E R I).
          Proof.  
            repeat intro.
            subst. eapply eq_itree_iter. intros ?? <-. apply H.
          Qed.
      
          #[global] Instance missing_iter_instance' {E R I}:
            Proper (pointwise_relation I (eutt eq) ==> eq ==> eutt eq) (@ITree.iter E R I).
          Proof.  
            repeat intro.
            subst. eapply eutt_iter' with (RI := eq).
            intros ?? <-. rewrite H. all: reflexivity.
          Qed.
          
          Theorem denote_imp_fold_constants_stmt : forall s,
              denote_imp  (fold_constants_stmt s) ≅ denote_imp s.
          Proof.
            intros s; induction s.
            - cbn; now rewrite denote_imp_fold_constants_expr.
            - cbn. now setoid_rewrite IHs1; setoid_rewrite IHs2.
            - cbn.
              rewrite <- (denote_imp_fold_constants_expr i).
              destruct (fold_constants_expr i) eqn:eqi.
              all: cbn.
              all: try bind.
              all: try now case is_true; eauto.
              destruct v; subst; rewrite bind_ret_l.
              now cbn; rewrite IHs2.
              now cbn; rewrite IHs1.
            - assert (BASE_CASE: forall (t : expr),
                         denote_imp  (WHILE (fold_constants_expr t) DO (fold_constants_stmt s)) ≅
                         denote_imp (WHILE t DO s)
                     ).
              { clear t; intros t.
                cbn.
                eapply eq_itree_iter; intros ?? <-.
                try (rewrite denote_imp_fold_constants_expr; bind).
                case is_true; try reflexivity.
                try now rewrite IHs.
              }
              cbn.
              destruct (fold_constants_expr t) eqn:eqt; [| destruct v |..];
            try (rewrite <- eqt; apply BASE_CASE).
              unfold while.
              (* HERE *)
              setoid_rewrite <- (denote_imp_fold_constants_expr t).
                rewrite eqt.
          cbn.
          rewrite unfold_iter_ktree.
          rewrite ? bind_ret_l.
          now cbn; rewrite ? bind_ret_l.
  
        - reflexivity.
        - reflexivity. Qed.
      
      Theorem denote_imp_fold_constants_expr_weak : forall e,
          denote_expr (fold_constants_expr e) ≈ denote_expr e.  
      Proof. 
        intros.
        induction e.
        - simpl. reflexivity.
        - simpl. reflexivity.
        -  unfold denote_expr. fold denote_expr. rewrite <- IHe1. 
          setoid_rewrite <- IHe2. simpl. destruct (fold_constants_expr e1) eqn:He1; 
            destruct (fold_constants_expr e2) eqn:He2; simpl; try reflexivity. rewrite bind_ret_l. rewrite bind_ret_l. reflexivity.
        - unfold denote_expr. fold denote_expr. rewrite <- IHe1.
          setoid_rewrite <- IHe2. simpl. destruct (fold_constants_expr e1) eqn:He1; 
            destruct (fold_constants_expr e2) eqn:He2; simpl; try reflexivity. rewrite bind_ret_l. rewrite bind_ret_l. reflexivity.
        - unfold denote_expr. fold denote_expr. rewrite <- IHe1.
          setoid_rewrite <- IHe2. simpl. destruct (fold_constants_expr e1) eqn:He1; 
            destruct (fold_constants_expr e2) eqn:He2; simpl; try reflexivity. rewrite bind_ret_l. rewrite bind_ret_l. reflexivity.
      Qed.
      
      
      Theorem denote_imp_fold_constants_stmt_weak : forall s,
          denote_imp (fold_constants_stmt s) ≈ denote_imp s.
      Proof.
        induction s. intros. 
        -  simpl. rewrite denote_imp_fold_constants_expr_weak. reflexivity.
        - simpl. rewrite IHs1. setoid_rewrite IHs2. reflexivity.
        - simpl.
           rewrite <- denote_imp_fold_constants_expr_weak.
          destruct (fold_constants_expr i). 
          + apply eqit_bind. reflexivity. 
            red.
            simpl. intros. destruct a; simpl; try reflexivity.
            rewrite IHs2. reflexivity.
            rewrite IHs1. reflexivity.
          + destruct v.
            * simpl. rewrite bind_ret_l. simpl. rewrite IHs2. reflexivity.
            * simpl. rewrite bind_ret_l. simpl. rewrite IHs1. reflexivity.
          + apply eqit_bind. reflexivity. 
            red.
            simpl. intros. destruct a; simpl; try reflexivity.
            rewrite IHs2. reflexivity.
            rewrite IHs1. reflexivity.
          + apply eqit_bind. reflexivity. 
            red.
            simpl. intros. destruct a; simpl; try reflexivity.
            rewrite IHs2. reflexivity.
            rewrite IHs1. reflexivity.
          + apply eqit_bind. reflexivity.
              red.
              simpl. intros. destruct a; simpl; try reflexivity.
              rewrite IHs2. reflexivity.
              rewrite IHs1. reflexivity.
        - assert (BASE_CASE: forall (t : expr),
          denote_imp  (WHILE (fold_constants_expr t) DO (fold_constants_stmt s)) ≈
          denote_imp (WHILE t DO s)
      ).
      { intros.
      simpl. apply eutt_iter' with (RI := eq).
      intros _ _ []. apply eutt_clo_bind with (UU := eq); try reflexivity.
      apply denote_imp_fold_constants_expr_weak.
      intros. subst. destruct u2. simpl. reflexivity. simpl. rewrite IHs. reflexivity. reflexivity. 
      }
      cbn. destruct (fold_constants_expr t) eqn:eqt; [| destruct v |..].
      + rewrite <- eqt. apply BASE_CASE.
      + unfold while. unfold while. unfold iter. unfold Iter_Kleisli. unfold Basics.iter. unfold MonadIter_itree.
        simpl.
        rewrite unfold_iter. rewrite bind_bind.
        rewrite <- denote_imp_fold_constants_expr_weak. rewrite eqt. simpl.
        rewrite bind_ret_l. simpl. rewrite bind_ret_l. reflexivity.
      + rewrite <- eqt. apply BASE_CASE.
      + rewrite <- eqt. apply BASE_CASE.
      + rewrite <- eqt. apply BASE_CASE.
      + rewrite <- eqt. apply BASE_CASE. 
      - simpl. reflexivity.
        - simpl. reflexivity.
          Qed. 
        
       
      Theorem CAsgn_congruence : forall x a a',
          denote_expr a  ≅ denote_expr a' ->
          denote_imp (Assign x a) ≅ denote_imp (Assign x a').
        Proof.  
          intros x a a' Heqv.  
          simpl. rewrite Heqv. reflexivity. Qed.
      
      Theorem CAsgn_congruence_weak : forall x a a',
          denote_expr a  ≈ denote_expr a' ->
          denote_imp (Assign x a) ≈ denote_imp (Assign x a').
        Proof.  
          intros x a a' Heqv.  
          simpl. rewrite Heqv. reflexivity. Qed.
      
      Theorem CSeq_congruence : forall c1 c1' c2 c2',
          denote_imp c1 ≅ denote_imp c1' ->
          denote_imp c2 ≅ denote_imp c2' ->
          denote_imp (Seq c1 c2) ≅ denote_imp (Seq c1' c2').
        Proof.
          intros c1 c1' c2 c2' Heqc1 Heqc2.
          simpl. apply eqit_bind.
          - rewrite Heqc1. reflexivity.
          - intros. setoid_rewrite Heqc2. reflexivity. Qed.
      
        Theorem CSeq_congruence_weak : forall c1 c1' c2 c2',
          denote_imp c1 ≈ denote_imp c1' ->
          denote_imp c2 ≈ denote_imp c2' ->
          denote_imp (Seq c1 c2) ≈ denote_imp (Seq c1' c2').
        Proof.
          intros c1 c1' c2 c2' Heqc1 Heqc2.
          simpl. apply eqit_bind.
          - rewrite Heqc1. reflexivity.
          - intros. setoid_rewrite Heqc2. reflexivity. Qed.
      
        Theorem CIf_congruence : forall i i' t t' e e',
            denote_expr i ≅ denote_expr i' ->
            denote_imp t ≅ denote_imp t' ->
            denote_imp e ≅ denote_imp e' ->
            denote_imp (If i t e) ≅ denote_imp (If i' t' e').
        Proof.
          intros i i' t t' e e' Heqi Heqt Heqe.
          simpl. rewrite Heqi.
          apply eqit_bind; [ reflexivity | ].
          intros []. case is_true; auto. 
          simpl. rewrite Heqt. reflexivity. 
          
          Qed.
      
        Theorem CIf_congruence_weak : forall i i' t t' e e',
            denote_expr i ≈ denote_expr i' ->
            denote_imp t ≈ denote_imp t' ->
            denote_imp e ≈ denote_imp e' ->
            denote_imp (If i t e) ≈ denote_imp (If i' t' e').
        Proof.
          intros i i' t t' e e' Heqi Heqt Heqe.
          simpl. rewrite Heqi.
          apply eqit_bind; [ reflexivity | ].
          intros []. case is_true; auto. 
          simpl. rewrite Heqt. reflexivity. 
          
          Qed.
      
        Theorem CWhile_congruence : forall t t' b b',
            denote_expr t ≅ denote_expr t' ->
            denote_imp b ≅ denote_imp b' ->
            denote_imp (While t b) ≅ denote_imp (While t' b').
      
      
        Proof.
          intros t t' b b' Heqt Heqb.
          simpl. unfold while.
          eapply eq_itree_iter; intros ?? <-.
          apply eqit_bind.
          rewrite Heqt. reflexivity.
      
          intros []. case is_true; auto.
          simpl. rewrite Heqb. reflexivity. reflexivity.
          simpl. rewrite Heqb. reflexivity.
          Qed.
      
       
        Theorem CWhile_congruence_weak : forall t t' b b',
            denote_expr t ≈ denote_expr t' ->
            denote_imp b ≈ denote_imp b' ->
            denote_imp (While t b) ≈ denote_imp (While t' b').
        Proof.
          intros t t' b b' Heqt Heqb.
          simpl. unfold while.
          apply eutt_iter' with (RI := eq). intros _ _ []. apply eutt_clo_bind with (UU := eq); try reflexivity.
          assumption. intros. subst. destruct u2. simpl. reflexivity. simpl. rewrite Heqb. reflexivity. reflexivity.
          Qed.
          
      
      
          Theorem denote_imp_fold_constants_stmt_with_congruence : forall s,
              denote_imp (fold_constants_stmt s) ≅ denote_imp s.
          Proof.
            intros s; induction s.
            - apply CAsgn_congruence. apply denote_imp_fold_constants_expr.
            -  unfold fold_constants_stmt. fold fold_constants_stmt.
               apply CSeq_congruence; try reflexivity.
               apply IHs1. apply IHs2.
            - unfold fold_constants_stmt. 
              fold fold_constants_stmt.
              unfold denote_imp. fold denote_imp.
              rewrite <- (denote_imp_fold_constants_expr i).
              destruct (fold_constants_expr i) eqn:eqi.
              + apply CIf_congruence; try reflexivity. 
                apply IHs1. apply IHs2.
              + destruct v.
                * simpl. rewrite bind_ret_l. simpl.  
                  apply IHs2.
                * simpl. rewrite bind_ret_l. simpl.  
                  apply IHs1.
              + apply CIf_congruence; try reflexivity.
                apply IHs1. apply IHs2.
              + apply CIf_congruence; try reflexivity.
                apply IHs1. apply IHs2.
              + apply CIf_congruence; try reflexivity.
                apply IHs1. apply IHs2.
            - unfold fold_constants_stmt. fold fold_constants_stmt.
              unfold denote_imp. fold denote_imp.
              unfold while.
              setoid_rewrite <- (denote_imp_fold_constants_expr t).
                destruct (fold_constants_expr t) eqn:eqt; 
                try apply CWhile_congruence; try reflexivity; try apply IHs.
                * destruct v. simpl.
                  unfold iter. unfold Iter_Kleisli. unfold Basics.iter. unfold MonadIter_itree.
                  rewrite unfold_iter. rewrite bind_bind.
                  
                  rewrite bind_ret_l. simpl. rewrite bind_ret_l. reflexivity.
                  apply CWhile_congruence; try reflexivity. apply IHs.
          - simpl.  reflexivity.
            - reflexivity.
          Qed.
      
          Theorem denote_imp_fold_constants_stmt_with_congruence_weak : forall s,
              denote_imp (fold_constants_stmt s) ≈ denote_imp s.
          Proof.
            intros s; induction s.
            - apply CAsgn_congruence_weak. apply denote_imp_fold_constants_expr_weak.
            -  unfold fold_constants_stmt. fold fold_constants_stmt.
               apply CSeq_congruence_weak; try reflexivity.
               apply IHs1. apply IHs2.
            - unfold fold_constants_stmt. 
              fold fold_constants_stmt.
              unfold denote_imp. fold denote_imp.
              rewrite <- (denote_imp_fold_constants_expr_weak i).
              destruct (fold_constants_expr i) eqn:eqi.
              + apply CIf_congruence_weak; try reflexivity. 
                apply IHs1. apply IHs2.
              + destruct v.
                * simpl. rewrite bind_ret_l. simpl.  
                  apply IHs2.
                * simpl. rewrite bind_ret_l. simpl.  
                  apply IHs1.
              + apply CIf_congruence_weak; try reflexivity.
                apply IHs1. apply IHs2.
              + apply CIf_congruence_weak; try reflexivity.
                apply IHs1. apply IHs2.
              + apply CIf_congruence_weak; try reflexivity.
                apply IHs1. apply IHs2.
            - unfold fold_constants_stmt. fold fold_constants_stmt.
              unfold denote_imp. fold denote_imp.
              unfold while.
               
              setoid_rewrite <- (denote_imp_fold_constants_expr_weak t).
                destruct (fold_constants_expr t) eqn:eqt; 
                try apply CWhile_congruence_weak; try reflexivity; try apply IHs.
                * destruct v. simpl. rewrite unfold_iter_ktree. rewrite ? bind_ret_l. 
                  now cbn; rewrite ? bind_ret_l.
                  apply CWhile_congruence_weak; try reflexivity. apply IHs.
          - simpl.  reflexivity. 
            - reflexivity.
              Qed.
              
      
      
  
          