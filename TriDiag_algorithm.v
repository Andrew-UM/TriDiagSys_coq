Require Import Coq.Reals.Reals.
Require Import Coq.Vectors.Vector.
Import VectorNotations.


Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.


Definition vector := Vector.t. 

Record TriDiagSys (n : nat) := {
  c : vector R n;
  b : vector R (S n);
  a : vector R n;
  f : vector R (S n);
}.

(* Operations on elements of type R *)
Definition sub (a b : R) : R := Rminus a b. (* Subtraction *)
Definition mul (a b : R) : R := Rmult a b.  (* Multiplication *)
Definition div (a b : R) : R := Rdiv a b.    (* Division *)
Definition one : R := R1.                    (* Identity element for multiplication *)
Definition zero : R := R0.                   (* Identity element for addition *)
Definition add (a b : R) : R := Rplus a b.    (* Addition *)

(* Функция для вычисления denominator *)
(* denominator = b[i] + a[i]*alpha[i]; *)
Definition denominator (a alpha b : R) : R :=
  add (mul a alpha) b.

(* Функция для вычисления a_i *)
(* alpha[i+1] = -c[i]  / denominator; i>=0 *)
Definition alpha_i (c a alpha b : R) : R :=
  div (sub zero c) (denominator a alpha b).

(* Функция для вычисления a_1 *)
(* alpha[0] = -c[0] / b[0]; *)
Definition alpha_1 (c b : R) : R :=
  div (sub zero c) b.
  
(* Функция для вычисления b_i *)
(* beta[i+1] = (f[i] - a[i]*beta[i]) / denominator; i>=0*)
Definition beta_i (a b f alpha beta : R) : R :=
  div (sub f (mul a beta)) (denominator a alpha b).

(* Функция для вычисления b_1 *)
(* beta[0] = f[0]  / b[0]; *)
Definition beta_1 (f b : R) : R :=
  div f b.

(* Функция для вычисления x_j, j<n*)
(*  *)
Definition x_j (x alpha beta : R) : R :=
  add (mul alpha x) beta.

(* Функция для вычисления x_n*)
(*  *)
Definition x_n (a b f alpha beta  : R) : R :=
  div (sub f (mul a beta)) (add b (mul a alpha)).

Fixpoint mkVector (n : nat) (value : R) : Vector.t R n :=
match n with
| O => Vector.nil R
| S p => value :: (mkVector p value)
end.


Fixpoint matrix_mul' (n : nat) (a b x : vector R (S n)) (c : vector R n) (x_i : R) : vector R (S n) :=
  match n return vector R (S n) -> vector R (S n) -> vector R (S n) -> vector R n -> vector R (S n) with
  | 0 => fun a b x c =>
    let a_1 := hd a in
    let b_1 := hd b in
    let x_1 := hd x in
    let f_n := add (mul a_1 x_i) (mul b_1 x_1) in
    [f_n]
  | S k => fun a b x c =>
    let a_1 := hd a in
    let tla := tl a in
    let b_1 := hd b in
    let tlb := tl b in
    let c_1 := hd c in
    let tlc := tl c in
    let x_1 := hd x in
    let tlx := tl x in
    let x_2 := hd tlx in
    let f_1 := mul a_1 x_i in
    let f_2 := mul b_1 x_1 in
    let f_3 := mul c_1 x_2 in
    let f := add f_1 (add f_2 f_3) in
    f :: (matrix_mul' k tla tlb tlx tlc x_1)
  end a b x c.


Definition matrix_mul {n : nat} (SLE : TriDiagSys n) (x : vector R (S n)) : vector R (S n) :=
  match n return TriDiagSys n -> vector R (S n) -> vector R (S n) with
  | 0 => fun SLE x =>
    let b_1 := hd (b _ SLE) in
    let x_1 := hd x in
    let f_1 := mul b_1 x_1 in
    [f_1]
  | S k => fun SLE x =>
    let b_1 := hd (b _ SLE) in
    let tlb := tl (b _ SLE) in
    let c_1 := hd (c _ SLE) in
    let tlc := tl (c _ SLE) in
    let x_1 := hd x in
    let tlx := tl x in
    let x_2 := hd tlx in
    let f_1 := add (mul b_1 x_1) (mul c_1 x_2) in
    f_1 :: (matrix_mul' k (a _ SLE) tlb tlx tlc x_1)
  end SLE x.



Fixpoint find_alpha' (n : nat) (b : vector R (S n)) (a c : vector R n) (alpha : R) : vector R n :=
  match n return vector R (S n) -> vector R n -> vector R n -> vector R n with
  | O => fun _ _ _ => []
  | S k => fun b a c =>
    let b_1 := hd b in
    let tlb := tl b in
    let a_1 := hd a in
    let tla := tl a in
    let c_1 := hd c in
    let tlc := tl c in
    let alpha_i := alpha_i c_1 a_1 alpha b_1 in
    alpha_i :: (find_alpha' k tlb tla tlc alpha_i) 
  end b a c. 


Definition find_alpha {n : nat} (SLE : TriDiagSys n) : vector R (S n) :=
  match n return TriDiagSys n -> vector R (S n) with
  | O => fun _ => [0%R] (* этот случай не возникает, так как случай n=0 отдельно обрабатывается в solution *)
  | S k => fun SLE =>
    let c_1 := hd (c _ SLE) in
    let b_1 := hd (b _ SLE) in
    let alpha_1 := alpha_1 c_1 b_1 in
    alpha_1 :: (find_alpha' (S k) (b _ SLE) (c _ SLE) (a _ SLE) alpha_1)
  end SLE.


Fixpoint find_beta' (n : nat) (b f alpha: vector R (S n)) (a : vector R n) (beta : R) : vector R n :=
  match n return vector R (S n) -> vector R (S n) -> vector R (S n) -> vector R n -> vector R n with
  | O => fun _ _ _ _ => []
  | S k => fun b f alpha a =>
    let a_1 := hd a in
    let tla := tl a in
    let b_1 := hd b in
    let tlb := tl b in
    let f_1 := hd f in
    let tlf := tl f in
    let hd_alpha := hd alpha in
    let tl_alpha := tl alpha in
    let beta_i := beta_i a_1 b_1 f_1 hd_alpha beta in
    beta_i :: (find_beta' k tlb tlf tl_alpha tla beta_i)
end b f alpha a. 


Definition find_beta {n : nat} (SLE : TriDiagSys n) (alpha : vector R (S n)) : vector R (S n) :=
  match n return TriDiagSys n -> vector R (S n) -> vector R (S n) with
  | O => fun _ _ => [0%R] (* этот случай не возникает, так как случай n=0 отдельно обрабатывается в solution *)
  | S k => fun SLE alpha =>
    let b_1 := hd (b _ SLE) in
    let f_1 := hd (f _ SLE) in
    let beta_1 := beta_1 f_1 b_1 in
    beta_1 :: (find_beta' (S k) (b _ SLE) (f _ SLE) alpha (a _ SLE) beta_1)
  end SLE alpha.


Fixpoint find_x' (n : nat) (alpha beta : vector R (S n)) (x : R) : vector R (n) :=
  match n return vector R (S n) -> vector R (S n) -> vector R n with
  | O => fun _ _ => []
  | S k => fun alpha beta =>
    let hd_alpha := hd alpha in
    let tl_alpha := tl alpha in
    let hd_beta := hd beta in
    let tl_beta := tl beta in
    let x_j := x_j x hd_alpha hd_beta in
    x_j :: (find_x' k tl_alpha tl_beta x_j)
  end alpha beta.

  
Definition find_x {n : nat} (SLE : TriDiagSys n) (alpha beta : vector R (S n)) : vector R (S n) :=
match n return TriDiagSys n -> vector R (S n) -> vector R (S n) -> vector R (S n) with
  | O => fun _ _ _ => [0%R] (* этот случай не возникает, так как случай n=0 отдельно обрабатывается в solution *)
  | S k => fun SLE alpha beta =>
    let a' := rev (a _ SLE) in
    let b' := rev (b _ SLE) in
    let f' := rev (f _ SLE) in
    let alpha' := rev (alpha) in
    let beta' := rev (beta) in
    let a_n := hd a' in
    let b_n := hd b' in
    let f_n := hd f' in
    let alpha_n := hd alpha' in
    let beta_n := hd beta' in
    let x_n := x_n a_n b_n f_n alpha_n beta_n in
    rev (x_n :: (find_x' (S k) alpha' beta' x_n) )
  end SLE alpha beta.


Definition solution {n : nat} (SLE : TriDiagSys n) : vector R (S n) :=
  match n return TriDiagSys n -> vector R (S n) with
  | 0 => fun SLE => 
    let b_1 := hd (b _ SLE) in
    let f_1 := hd (f _ SLE) in
    let x_1 := div f_1 b_1 in
    [x_1]
  | S k => fun SLE =>
    let alpha := find_alpha SLE in
    let beta := find_beta SLE alpha in
    find_x SLE alpha beta
  end SLE.


Fixpoint find_denominator' (n : nat) (b : vector R (S n)) (a c : vector R n) (alpha : R) : vector R n :=
  match n return vector R (S n) -> vector R n -> vector R n -> vector R n with
  | O => fun _ _ _ => []
  | S k => fun b a c =>
    let b_1 := hd b in
    let tlb := tl b in
    let a_1 := hd a in
    let tla := tl a in
    let c_1 := hd c in
    let tlc := tl c in
    let denominator := denominator a_1 alpha b_1 in
    let alpha_i := alpha_i c_1 a_1 alpha b_1 in
    denominator :: (find_denominator' k tlb tla tlc alpha_i) 
  end b a c. 


Definition find_denominator {n : nat} (SLE : TriDiagSys n) : vector R (S n) :=
  match n return TriDiagSys n -> vector R (S n) with
  | O => fun _ => 
    let b_1 := hd (b _ SLE) in
    [b_1]
  | S k => fun SLE =>
    let c_1 := hd (c _ SLE) in
    let b_1 := hd (b _ SLE) in
    let denominator :=  b_1 in
    let alpha_1 := alpha_1 c_1 b_1 in
    denominator :: (find_denominator' (S k) (b _ SLE) (c _ SLE) (a _ SLE) alpha_1) 
    end SLE.


