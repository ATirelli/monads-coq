Add LoadPath "./" as Monads .
(*Require Import Monads.FunctorApplicativeMonad.*)
Require Import Monads.ExnMonad.
(*Require Import Monads.ExnTransformer.*)
Require Import NPeano Arith Bool String List.

Definition state:= string -> nat.
Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Definition state_update  (m : state )
                    (x : string) (v : nat) :=
  fun x' => if eqb_string x x' then v else m x'.
  
Definition newarray (n : nat) : state :=
  (fun _ => n).

Notation "'_' '!->' v" := (newarray v)
  (at level 100, right associativity).

Definition empty_st := (_ !-> 0).


Inductive exp : Type :=
  | ANum (n : nat)
  | AId (x : string)             
  | APlus (a1 a2 : exp)
  | ADiv (a1 a2: exp)
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
Notation "x / y" := (ADiv x y) (in custom com at level 50, left associativity).
Notation "x == y" := (EqExp x y) (in custom com at level 50, left associativity).
Open Scope com_scope.

Definition X:string:="x"%string.
Definition Y:string:="y"%string.
Definition Z:string:="z"%string.

Inductive com : Type :=
  | CSkip 
  | CAss (x : string) (a : exp)
  | CSeq (c1 c2 : com)
  | CIf (a: exp) (c1 c2 : com)
  | CWhile (a: exp) (c: com).

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


Fixpoint eval (a : exp) :(state-> exn nat) :=
  match a with
  | ANum n       => fun s => Result n
  | AId x        => fun s => Result (s x)  
  | <{a1 + a2}>  => fun s => let n1:= (eval a1 s) in let n2:= (eval a2 s) in 
                                match n1 with 
                                  | Fail s    => Fail s
                                  | Result m1 => match n2 with 
                                        | Fail s => Fail s
                                        | Result m2 => Result (m1 + m2) end end 
  | <{a1 / a2}>  => fun s => let n1:= (eval a1 s) in let n2:= (eval a2 s) in 
                                match n1 with 
                                  | Fail s    => Fail s
                                  | Result m1 => match n2 with 
                                        | Fail s => Fail s
                                        | Result m2 => match m2 with 
                                                 | 0 => Fail "Division by zero!"
                                                 | _ => Result (m1/m2) end end end 
  | <{a1 == a2}> => fun s => let n1:= (eval a1 s) in let n2:= (eval a2 s) in 
                                match n1 with 
                                  | Fail s    => Fail s
                                  | Result m1 => match n2 with 
                                        | Fail s => Fail s
                                        | Result m2 => match (beq_nat m1 m2) with 
                                                        | true     => Result 0
                                                        | false    => Result 1
                                                                          end end end end .

Example ex:exp := <{X+Y/Z+1}>.
Compute  (eval ex (newarray 1)). 
Compute  (eval ex empty_st). 

Definition assign (x:string) (n:nat)(s: state):state := state_update s x n. 
  
Fixpoint exec (c: com)(fuel: nat): (state -> exn(unit * state)) :=
match fuel with 
| 0       => fun s=> Fail "Gas finished before end of program! Try executing with more gas."
| S fuel' => match c with 
        | <{ skip }>    => fun s => Result (tt, s)
        | <{ x := a }>  => fun s => let m:=(eval a s) in match m with 
                                                | Result n => Result (tt, state_update s x n)
                                                | Fail str => Fail str end 
        | <{c1; c2}>    => fun s => let o:= (exec c1 fuel') in match (o s) with 
                                                | Fail str => Fail str
                                                | Result (a, s') => 
                                                    let o':= (exec c2 fuel') in (o' s') end 
        | <{if a then c1 else c2 end}> => fun s => let m:=(eval a s) in match m with
                                                | Fail str => Fail str 
                                                | Result n => match n with 
                                                          | 0 => (exec c1 fuel') s
                                                          | _ => (exec c2 fuel') s end end 
        |<{while b do c1 end}> => fun s => let m:=(eval b s) in match m with
                                                | Fail str => Fail str
                                                | Result b1 => match b1 with 
                                                        | S _ => Result (tt, s)
                                                        | 0   => match ((exec c1 fuel') s) with 
                                                               | Result (a, s') => (exec c fuel') s'
                                                               | Fail str => Fail str end end end 
end end .
                                                          
Definition fact_in_coq : com :=
  <{ Z := 5;
     Y := 1;
     while X do
       if Y == 100 then 
         X:=1 
       else
         Y := Y+1
       end
      end
     }>.

Definition eval_on_exn_state(es: exn (unit*state))(s: string): exn  nat:=
match es with 
| Fail str => Fail str 
| Result (a, st) => Result (st s) end. 



Compute  eval_on_exn_state((exec fact_in_coq 20) empty_st) Y.
   
   
 