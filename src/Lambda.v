Require Import Monads.Tactics.
Require Import Monads.Utils.
Require Import Monads.DelayMonad.
From Coq Require Import List Lia Arith.

CoInductive Computation (A:Type) : Type :=
| Return : A -> Computation A
| Bind : forall (B:Type), Computation B-> (B-> Computation A)-> Computation A.
Arguments Return {A}.
Arguments Bind {A B}.
Notation "c >>= f" := (Bind c f) (at level 20).
Notation "var <- c ; rest" :=
(Bind c (fun var => rest) )
(at level 60, right associativity).


Definition OptPartial (A: Type):= Partial (option A).
Definition fail {A: Type}:= rtrn (@None A).
Print fail.

Definition ret {A: Type}(x: A):= rtrn (Some x).
Print ret.

CoFixpoint bind {A B: Type}(x: OptPartial A) (f: A -> OptPartial B): OptPartial B :=
match x with 
| rtrn None => fail
| rtrn (Some x) => f x
| step y => step (bind y f) end.

Notation "var <-- c ;; rest" :=
(bind c (fun var => rest) )
(at level 60, right associativity).


Definition CompPartial (A: Type) := Computation (OptPartial A).
Parameter const: Type.

Inductive term: Type :=
  | Var: nat -> term
  | Const: const -> term
  | Fun: term -> term
  | App: term -> term -> term.

Inductive value: Type :=
  | Int: const -> value
  | Clos: term -> list value -> value.

Definition env := list value.
Definition Fail {A: Type}:= Return (@fail A).


Definition Ret {A: Type}(x: A):= Return (ret x).
Print Ret.

Definition demonad {A: Type} (x: CompPartial A):=
match x with 
| Return t => t
| _ => fail end.

CoFixpoint bs (t: term) (e:env): (CompPartial value) :=
match t with 
 | Const i => Ret (Int i)
 | Var n   => match (nth_error e n) with 
           | Some v => Ret v
           | None   => Fail end
 | Fun a => Ret (Clos a e) 
 | App a b => op1 <- bs a e ; op2 <- bs b e ; 
                        Return (v1 <-- op1 ;; v2 <-- op2 ;; match v1 with 
                                    | Int n    => fail 
                                    | Clos x y => fail end)
                                                   end.

