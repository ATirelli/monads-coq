Require Import Monads.OuputMonad.
Require Import Monads.FunctorApplicativeMonad.
Require Import NPeano Arith Bool String List.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)) 
                             (right associativity, at level 84, c1 at next level).

Notation "c1 ;; c2" := (bind c1 (fun _ => c2)) (at level 100, right associativity).


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

Inductive tm := 
| Con : nat -> tm
| Div : tm -> tm -> tm.

Example answer: tm := (Div (Div (Con 1972 ) (Con 2 )) (Con 23 )).
Example error: tm := (Div (Con 1)(Con 0)).


Instance expShow : Show tm := {
  show := fix show_exp (t:tm) : string := 
              match t with 
                | Con n => "(Con "++ show n ++")"
                | Div t1 t2 => "(Div " ++ (show_exp t1) ++ (show_exp t2) ++ ")"
              end %string
}.

Definition line(t:tm) (n:nat):string:=
(append (append "eval"%string (show (t))) (append "<="%string (append (show n ) "
      "%string))).

Fixpoint eval_output (t:tm) : output nat  := 
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

