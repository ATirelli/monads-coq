(* Porting the beating approach to coq*)
From Coq Require Import List Lia Arith.
Set Implicit Arguments.

(* The original partiality monad*)
CoInductive C (A:Type) : Type :=
| Return : A -> C A
| Step : C A -> C A.
Arguments Return {A}.
Arguments Step {A}.

(* the reified one*)
CoInductive CP (A:Type) : Type :=
| PReturn : A -> CP A
| PBind : forall (B:Type), CP B-> (B-> CP A)-> CP A
| PFail
| PStep : CP A -> CP A.
Arguments PReturn {A}.
Arguments PBind {A B}.
Arguments PStep {A}.
Arguments PFail {A}.

(* The weak normal form of reification*)
CoInductive CW (A:Type) : Type :=
| WReturn : A -> CW A
| WFail
| WStep : CW A -> CW A.

Arguments WReturn {A}.
Arguments WStep {A}.
Arguments WFail {A}.


(* must be a cofix/fix combo -- but for some reason itìs not defined, so I cannot use it later *)
(*Program CoFixpoint whnf {A:Type} (cp : CP A)  : CW A :=
  match cp with
  | PFail => WFail 
  | PReturn x => WReturn x
  | PStep x => WStep (whnf  x)
  |PBind  c f => WBind (whnf c) f
                    end

with 
(* CoFixpoint *)
  WBind {A B}  (x: CW A) (f: A -> CP B) {struct x}: CW B := 
  match x with
    | WFail => WFail
| WReturn y => whnf ( f y) 
| WStep t => WStep (WBind  t f) end.
Next Obligation.
  - auto.
    Defined.
*)

(*
      ⟪_⟫W : ∀ {A} → Maybe A ⊥W → Maybe A ⊥
      ⟪ fail     ⟫W = PF.fail
      ⟪ return x ⟫W = PF.return x
      ⟪ later x  ⟫W = later (♯ ⟪ x ⟫P)

    ⟪_⟫P : ∀ {A} → Maybe A ⊥P → Maybe A ⊥
    ⟪ p ⟫P = ⟪ whnf p ⟫W
*)

(*CoFixpoint execW {A}(w : CW A) : C (option A) :=
  match w with
  |WFail => Return None
  |WReturn x => Return (Some x)
  | WStep x => Step (execW  x) end
with
execP {A}(p : CP A) : C (option A) :=
  execW (whnf p).  (* undefined *)
  *)                 

