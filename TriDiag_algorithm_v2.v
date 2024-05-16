Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.RIneq.

Require Import Coq.Vectors.Vector.
Require Import Coq.Vectors.VectorSpec.

Import VectorNotations.
Open Scope R_scope.

Definition vector := Vector.t R.


Fixpoint mkVector (n : nat) (value : R) : Vector.t R n :=
match n with
| O => Vector.nil R
| S p => value :: (mkVector p value)
end.


Record TriDiagSys (n : nat) := {
  d : vector n;
  a : vector (S n);
  c : vector n;
  b : vector (S n);
}.


Record A_matrix (n : nat) := {
  d'' : vector n;
  a'' : vector (S n);
  c'' : vector n;
}.

Definition mkA {n : nat} (SLE : TriDiagSys n) :=
  let d := d _ SLE in
  let a := a _ SLE in
  let c := c _ SLE in
  Build_A_matrix _ d a c.

Definition mkA' {n : nat} (d c : vector n) (a : vector (S n)) :=
Build_A_matrix _ d a c.


Record L_matrix (n : nat) := {
  l : vector (S n);
  one_v : vector n;
}.

Definition mkL {n : nat} (l : vector (S n)) :=
  Build_L_matrix _ l (mkVector n 1). (* Не знаю как, но работает*)


Record U_matrix (n : nat) := {
  v : vector (S n); (* v[n] = 1, для задания определенного разложения *)
  u : vector n;
}.

Definition mkU {n : nat} (v : vector (S n)) (u : vector n) :=
  Build_U_matrix _ v u. (* Не знаю как, но работает*)


(* PART1 Вычисление разложения *)

Definition ui_find (ci li : R) : R :=
ci/li.

Definition vi_find (di : R) : R := 
di.

Definition l1_find (a1 v1 : R) : R :=
a1/v1.

Definition li_find (ai ui_ vi : R) : R :=
(ai - ui_) / vi.


Fixpoint v_find {n : nat} (d : vector n) : vector (S n) :=
  match n return vector n -> vector (S n) with
  | 0 => fun d => [1] 
  | S k => fun d =>
    let di := hd d in
    let tld := tl d in
    di :: v_find tld
  end d.


Record lu_vectors (n : nat) := { (* вспомогательный тип, для вычисления разложения, через рекурсию *)
  l' : vector (S n);
  u' : vector n;
}.

Definition mkLU {n : nat} (l : vector (S n)) (u : vector n) :=
  Build_lu_vectors _ l u.


Fixpoint find_LU' {n : nat} (a v : vector (S n)) (c : vector n) (ui_: R) : lu_vectors n:=
  match n return  vector (S n) -> vector (S n) -> vector n -> lu_vectors n with
  | 0 => fun  a v c =>
    let an := hd a in
    let ln := li_find an ui_ (hd v) in
    mkLU [ln] []
  | S k =>  fun a v c =>
    let ai := hd a in
    let ci := hd c in
    let vi := hd v in

    let tla := tl a in
    let tlc := tl c in
    let tlv := tl v in

    let li := li_find ai ui_ vi in
    let ui := ui_find ci li in

    let LU := find_LU' tla tlv tlc ui in

    let l' := l' _ LU in
    let u':= u' _ LU in

    let l := li :: l' in
    let u := ui :: u' in

    mkLU l u
  end a v c.


Definition find_LU {n : nat} (c : vector n) (a v : vector (S n)) : lu_vectors n :=
  match n return vector (S n) -> vector n -> vector (S n) -> lu_vectors n with
  | 0 => fun v c a => 
    let a1 := hd a in
    mkLU [a1] []
  | S k => fun v c a => 
    let a1 := hd a in
    let c1 := hd c in
    let v1 := hd v in

    let tla := tl a in
    let tlc := tl c in
    let tlv := tl v in

    let l1 := l1_find a1 v1 in
    let u1 := ui_find c1 l1 in

    let LU := find_LU' tla tlv tlc u1 in

    let l' := l' _ LU in
    let u':= u' _ LU in

    let l := l1 :: l' in
    let u := u1 :: u' in

    mkLU l u
  end v c a.


Definition make_L {n : nat} (SLE : TriDiagSys n) : L_matrix n :=

  let d := d _ SLE in
  let a := a _ SLE in
  let c := c _ SLE in

  let v := v_find d in

  let LU := find_LU c a v in
  let l := l' _ LU in
  mkL l.


Definition make_U {n : nat} (SLE : TriDiagSys n) : U_matrix n :=

  let d := d _ SLE in
  let a := a _ SLE in
  let c := c _ SLE in

  let v := v_find d in

  let LU := find_LU c a v in
  let u := u' _ LU in
  mkU v u.


Fixpoint LU_mul' {n : nat} (v l : vector (S  n))(u : vector n) (vi_ ui_ : R) : A_matrix n :=
  match n return vector (S n) -> vector (S n) -> vector n -> A_matrix n with
  | 0 => fun v l u =>
    let ln := hd l in
    let vn := hd v in
    let an := ui_ + (ln * vn) in
    mkA' [] [] [an]
  | S k => fun v l u =>
    let vi := hd v in
    let li := hd l in
    let ui := hd u in
    let tlv := tl v in
    let tll := tl l in
    let tlu := tl u in

    let ai := ui_ + (li * vi) in
    let ci := li * ui in

    let A := LU_mul' tlv tll tlu vi ui in
    let d' := d'' _ A in
    let a' := a'' _ A in
    let c' := c'' _ A in

    let d := vi :: d' in
    let a := ai :: a' in
    let c := ci :: c' in
    mkA' d c a 
  end v l u.


Definition LU_mul {n : nat} (L : L_matrix n) (U : U_matrix n) : A_matrix n :=
  let l := l _ L in
  let v := v _ U in
  let u := u _ U in
  match n return vector (S n) -> vector (S n) -> vector n -> A_matrix n with
    | 0 => fun l v u =>
      let l1 := hd l in
      let v1 := hd v in
      let a1 := l1 * v1 in
      mkA' [] [] [a1]
    | S k => fun l v u => 
      let l1 := hd l in
      let v1 := hd v in
      let u1 := hd u in
      let tlv := tl v in
      let tll := tl l in
      let tlu := tl u in
      
      let a1 := l1 * v1 in
      let c1 := l1 * u1 in

      let A := LU_mul' tlv tll tlu v1 u1 in

      let d' := d'' _ A in
      let a' := a'' _ A in
      let c' := c'' _ A in

      let d := v1 :: d' in
      let a := a1 :: a' in
      let c := c1 :: c' in
      mkA' d c a  
  end l v u.


(* Условия совместности *)

Fixpoint check_nonzero {n : nat} (v : vector n) : bool :=
  match v with
  | [] => true
  | h :: t => if Req_EM_T h 0 then false else check_nonzero t 
  end.


Definition magicL {n : nat} (L : L_matrix n) : Prop :=
  let l := l _ L in
  let l_not_zero := check_nonzero l in
  (l_not_zero = true).


Definition magicU {n : nat} (U : U_matrix n) : Prop :=
  let u := u _ U in
  let u_not_zero := check_nonzero u in
  (u_not_zero = true).


Definition is_consistent {n : nat} (SLE : TriDiagSys n) : Prop :=
  let L := make_L SLE in
  let U := make_U SLE in
  magicL L /\ magicU U.





(* Вспомогательные леммы*)

Lemma no_brackets : forall (r1 r2 r3 : R),
  (r1 * r2 * / r3)%R = (r1 * (r2 * / r3))%R.
Proof.
  intros r1 r2 r3.
  apply Rmult_assoc.
Qed.

Lemma hd_eq_one_v : forall (b : vector 1), [hd b] = b.
Proof.
intros b.
Admitted.


Lemma rev_one : forall (A : Type) (x : A),
  rev [x] = [x].
Proof.
  intros A x.
  unfold rev.
  simpl.
  unfold rev_append.
  simpl.
Admitted.

Lemma v0_eq_nil : forall (v : vector 0), v = [].
Proof.
intros.
Admitted.

Lemma vec_eq_hd_tl : forall {n : nat} (b : vector (S n)), b = hd b :: tl b.
Proof.
Admitted.

Lemma rev_hd_tl : forall {n : nat} (b : vector (S n)), rev (hd b :: tl b) = b.


(* Корректность построенного разложения*)

Lemma LU'_cor : forall {n : nat} (a : vector (S n)) (d c : vector n) (v0 u0 : R),
let v := v_find d in
LU_mul' v (l' _ (find_LU' a v c u0)) (u' _ (find_LU' a v c u0)) v0 u0 = mkA' d c a.
Proof.
intros n a d c.
induction n.
+
simpl.
intros.
unfold li_find.
unfold Rdiv.
rewrite Rinv_1.
rewrite Rmult_1_r.
rewrite Rmult_1_r.
unfold Rminus.
rewrite Rplus_comm.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite hd_eq_one_v.
rewrite (v0_eq_nil d).
rewrite (v0_eq_nil c).
reflexivity.
+
simpl. intros.
unfold LU_mul'.
unfold mkA'.
simpl.
rewrite IHn.
simpl.
rewrite <- vec_eq_hd_tl.
unfold li_find.
unfold Rdiv.
set (x := (hd a - u0)).
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m with (hd d) (x).
++
unfold x.
unfold Rminus.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_l.
rewrite <- vec_eq_hd_tl.
unfold ui_find.
rewrite Rmult_comm.
rewrite <- Rmult_assoc.
set (q := (hd a + - u0)).
unfold Rdiv.
rewrite Rinv_mult.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_inv.



admit.
++

Admitted.





Lemma LU_Decomposition:
  forall {n : nat} (SLE : TriDiagSys n), is_consistent SLE -> LU_mul (make_L SLE) (make_U SLE) = mkA SLE.
Proof.
intros.
induction n.
+
unfold LU_mul, make_L, make_U.
simpl.
destruct SLE as [d a c].
simpl.
rewrite Rmult_1_r.
rewrite hd_eq_one_v.
rewrite v0_eq_nil with c.
rewrite v0_eq_nil with d.
reflexivity.
+
unfold LU_mul, make_L, make_U.
simpl.
destruct SLE as [d a c].
simpl.
rewrite LU'_cor.
simpl.
unfold mkA'.
rewrite <- vec_eq_hd_tl.
unfold l1_find.
unfold Rdiv.
unfold ui_find.

Admitted.



(* PART2 Решение системы Ly = b *)

(* Поиск вектора-решений y *)

Definition y1_find (b1 l1 : R) : R :=
  b1/l1.

Definition yi_find (bi yi_ li : R) : R :=
  (bi - yi_) / li.


Fixpoint find_y' {n : nat} (b l : vector n) (yi_ : R) : vector n :=
  match n return vector n -> vector n -> vector n with
  | 0 => fun b l => []
  | S k => fun b l =>
    let bi := hd b in
    let li := hd l in
    let tlb := tl b in
    let tll := tl l in

    let yi := yi_find bi yi_ li in

    yi :: (find_y' tlb tll yi)
  end b l.


Definition find_y {n : nat} (L : L_matrix n) (b : vector (S n)) : vector (S n) :=
  let l := l _ L in

  let b1 := hd b in
  let l1 := hd l in
  let tlb := tl b in
  let tll := tl l in

  let y1 := y1_find b1 l1 in

  y1 :: (find_y' tlb tll y1).


(* Умножение матриц Ly *)

Fixpoint L_mul' {n : nat} (l y : vector n) (yi_ : R) : vector n :=
  match n return vector n -> vector n -> vector n with 
  | 0 => fun l y => []
  | S k => fun l y =>
    let li := hd l in
    let yi := hd y in
    let tll := tl l in
    let tly := tl y in

    let bi := yi_ + (li * yi) in
    bi :: (L_mul' tll tly yi)
  end l y.


Definition L_mul {n : nat} (L : L_matrix n) (y : vector (S n)) : vector (S n) :=
  let l := l _ L in

  let l1 := hd l in
  let y1 := hd y in
  let tll := tl l in
  let tly := tl y in
  
  let b1 := l1 * y1 in
  b1 :: (L_mul' tll tly y1).




(* Корректность найденного решения системы Ly = b *)


(* TODO добавить условие совместности *)
Lemma L_mul'_cor : forall {n : nat} (l' b : vector n) (y0 : R),
L_mul' l' (find_y' b l' y0) y0 = b.
Proof.
intros n l' b.
induction n.
+
intros.
unfold L_mul', find_y', yi_find.
simpl.
rewrite v0_eq_nil.
reflexivity.
+
simpl. intros.
set (y0' := (yi_find (hd b) y0 (hd l'))).
rewrite (IHn (tl l') ).
unfold y0'.
unfold yi_find.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
++
unfold Rminus.
rewrite <- Rplus_assoc.
rewrite Rplus_comm.
rewrite <- Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_comm.
rewrite Rplus_0_r.
rewrite <- vec_eq_hd_tl.
reflexivity.
++
(*TODO подкрутить совместность и отсутвие деления на 0*)

Admitted.


Lemma L_solution:
  forall {n : nat} (L : L_matrix n) (b : vector (S n)), magicL L -> L_mul (L) (find_y L b) = b.
Proof.
intros.
unfold L_mul, find_y.
simpl.
rewrite L_mul'_cor.
destruct L as [l].
simpl.
unfold y1_find.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
+
rewrite <- vec_eq_hd_tl.
reflexivity.
+
(*TODO подкрутить отсутвие деления на 0*)
Admitted.




(* PART3 Решение системы Ux = y *)

(* поиск вектора-решения x *)

Definition xn_find (yn vn : R) : R :=
  yn / vn.

Definition xi_find (yi ui xi_ vi: R) : R :=
  (yi - ui * xi_) / vi.


Fixpoint find_x' {n : nat} (y u v : vector n) (xi_ : R) : vector n :=
  match n return vector n -> vector n -> vector n -> vector n with
  | 0 => fun y u v => []
  | S k => fun y u v =>
    let vi := hd v in
    let yi := hd y in
    let ui := hd u in
    let initv := tl v in
    let inity := tl y in
    let initu := tl u in

    let xi := xi_find yi ui xi_ vi in

    xi :: (find_x' inity initu initv xi)
  end y u v.


Definition find_x {n : nat} (U : U_matrix n) (y : vector (S n)) : vector (S n) :=
  let u := rev (u _ U) in
  let v := rev (v _ U) in

  let vn := hd v in
  let yn := hd y in
  let initv := tl v in
  let inity := tl y in

  let xn := xn_find yn vn in

  rev (xn :: (find_x' inity u initv xn)).


(* умножение матриц Ux *)

Fixpoint U_mul' {n : nat} (x v u : vector n) (xi_ : R) : vector n :=
  match n return vector n -> vector n -> vector n -> vector n with
  | 0 => fun x u v => []
  | S k => fun x u v =>
    let vi := hd v in
    let xi := hd x in
    let ui := hd u in
    let initv := tl v in
    let initx := tl x in
    let initu := tl u in

    let yi := (vi * xi) + (ui * xi_) in
    yi :: (U_mul' initx initv initu xi)
  end x u v.


Definition U_mul {n : nat} (U : U_matrix n) (x : vector (S n)) : vector (S n) :=
  let u := rev (u _ U) in
  let v := rev (v _ U) in
  let x := rev x in

  let vn := hd v in
  let xn := hd x in
  let initv := tl v in
  let initx := tl x in

  let yn := vn * xn in
  (*TODO тут возможно есть косяк*)
  yn :: (U_mul' initx initv u xn).




(* Корректность найденного решения системы Ux = y *)



Lemma U_mul'_cor : forall {n : nat} (y u v : vector n) (x0 : R),
U_mul' (find_x' y u v x0) v u x0 = y.
Proof.
intros n y u v.
induction n.
+
intros.
unfold U_mul'.
rewrite v0_eq_nil.
reflexivity.
+
simpl. intros.
set (x0' := (xi_find (hd y) (hd y) x0 (hd v))).
rewrite IHn.
unfold x0', xi_find.  
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
++
rewrite Rmult_comm.
unfold Rminus.
rewrite Rplus_assoc.
rewrite Rplus_opp_l.
rewrite Rplus_0_r.
rewrite <- vec_eq_hd_tl.
reflexivity.
++
(*TODO подкрутить отсутвие деления на 0*)
Admitted.


Lemma U_solution:
  forall {n : nat} (U : U_matrix n) (y : vector (S n)), magicU U -> U_mul U (find_x U y) = y.
Proof.
intros.
unfold U_mul, find_x.
rewrite rev_rev.
destruct U as [v u].
simpl.
rewrite U_mul'_cor.
unfold xn_find.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
+
rewrite <- vec_eq_hd_tl.
reflexivity.
+
(*TODO подкрутить отсутвие деления на 0*)
Admitted.



(* PART4 Доказательство корректности алгоритма *)

(* Умножение матриц Ax *)

Fixpoint matrix_mul' (n : nat) (d a x : vector (S n)) (c : vector n) (xi : R) : vector (S n) :=
  match n return vector (S n) -> vector (S n) -> vector (S n) -> vector n -> vector (S n) with
  | 0 => fun d a x c =>
    let d1 := hd d in
    let a1 := hd a in
    let x1 := hd x in
    let fn := (d1 * xi) + (a1 * x1) in
    [fn]
  | S k => fun d a x c =>
    let d1 := hd d in
    let tld := tl d in
    let a1 := hd a in
    let tla := tl a in
    let c1 := hd c in
    let tlc := tl c in
    let x1 := hd x in
    let tlx := tl x in
    let x2 := hd tlx in
    let f1 := a1 * xi in
    let f2 := d1 * x1 in
    let f3 :=c1 * x2 in
    let f := f1 + f2 + f3 in
    f :: (matrix_mul' k tld tla tlx tlc x1)
  end d a x c.


Definition matrix_mul {n : nat} (SLE : A_matrix n) (x : vector (S n)) : vector (S n) :=
  match n return A_matrix n -> vector (S n) -> vector (S n) with
  | 0 => fun SLE x =>
    let a1 := hd (a'' _ SLE) in
    let x1 := hd x in
    let f1 := a1 * x1 in
    [f1]
  | S k => fun SLE x =>
    let a1 := hd (a'' _ SLE) in
    let tla := tl (a'' _ SLE) in
    let c1 := hd (c'' _ SLE) in
    let tlc := tl (c'' _ SLE) in
    let x1 := hd x in
    let tlx := tl x in
    let x2 := hd tlx in
    let f1 :=  (a1 * x1) + (c1 * x2) in
    f1 :: (matrix_mul' k (d'' _ SLE) tla tlx tlc x1)
  end SLE x.




(* Ассоциативность умножения матриц *)








Lemma matrix_mul'_cor : forall {n : nat}(L : L_matrix n) (U : U_matrix n) (x b : vector (S n)) (d0 x0 y0 v0 u0 : R),
let l := l _ L in
let u := u _ U in
let v := v _ V in


let LU' := LU_mul' v l u v0 u0 in
let a := a' _ LU' in
let d := d' _ LU' in
let c' := c' _ LU' in
let MM' := matrix_mul' d a x c

let 



Proof.
intros n.
induction n.
+
intros.
unfold matrix_mul', L_mul'.
unfold x, y.
unfold find_x, find_y'.
simpl.
admit.
+
simpl.
intros.
simpl.
rewrite IHn.
Admitted.

















Lemma LUx_assoc : forall {n : nat} (L : L_matrix n) (U : U_matrix n) (x : vector (S n)),
      matrix_mul (LU_mul L U) (x) = L_mul (L) (U_mul (U) (x)).
Proof.
intros.
induction n.
+ 
unfold matrix_mul, L_mul, U_mul.
simpl.
destruct L as [l].
destruct U as [v u].
simpl.
simpl.
rewrite <- hd_eq_one_v with (x).
rewrite rev_one.
simpl.
rewrite <- hd_eq_one_v with (v).
rewrite rev_one.
simpl.
rewrite <- Rmult_assoc.
reflexivity.
+
unfold matrix_mul, L_mul, LU_mul, U_mul.
simpl.
rewrite matrix_mul'_cor.




Admitted.




(* Теоерма о корректности найденного решения *)

Theorem correct:
  forall {n : nat} (SLE : TriDiagSys n), is_consistent SLE -> matrix_mul (mkA SLE) (find_x (make_U SLE) (find_y (make_L SLE) (b _ SLE))) = b _ SLE.
Proof.
intros.
rewrite <- LU_Decomposition.  
  +
  rewrite LUx_assoc.
  rewrite U_solution.
    ++
    rewrite L_solution.
      +++
      reflexivity.
      +++
      apply H.
    ++
    apply H.
  +
  apply H.
Qed.










Theorem correct':
  forall {n : nat} (SLE : TriDiagSys n), is_consistent SLE -> matrix_mul (mkA SLE) (find_x (make_U SLE) (find_y (make_L SLE) (b _ SLE))) = b _ SLE.
Proof.
intros.
induction n.
+
unfold matrix_mul, find_x, find_y, make_L, make_U.
simpl.
destruct SLE as [d a c b].
simpl.
unfold xn_find, y1_find.
admit.
+
unfold matrix_mul.

destruct SLE as [d a c b].
simpl.
pose (L := make_L {| d := d; a := a; c := c; b := b |}).
replace ((make_L {| d := d; a := a; c := c; b := b |})) with L.
++
pose (U := make_U {| d := d; a := a; c := c; b := b |}).
replace (make_U {| d := d; a := a; c := c; b := b |}) with U.
+++
rewrite <- L_solution.

admit.
+++
reflexivity.
++
reflexivity.

Qed.