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
(*Defenition*)
Definition check_nonzero {n : nat} (v : vector n) : Prop :=
Forall (fun h => h<>0) v.


Definition magicL {n : nat} (L : L_matrix n) : Prop :=
  let l := l _ L in
  check_nonzero l.


Definition magicU {n : nat} (U : U_matrix n) : Prop :=
  let v := v _ U in
  check_nonzero v.


Definition is_consistent {n : nat} (SLE : TriDiagSys n) : Prop :=
  let L := make_L SLE in
  let U := make_U SLE in
  magicL L /\ magicU U.


(* Вспомогательные леммы*)

Lemma vec_eq_hd_tl : forall {n : nat} (b : vector (S n)), b = hd b :: tl b.
Proof.
intros n b.
refine (match b with | nil _ => _ | cons _ _ _ _ => _ end).  
  +
    unfold IDProp.
    intros.
    apply H.
  +
    simpl.
    reflexivity.
Qed.


Lemma v0_eq_nil : forall (b : vector 0), b = [].
Proof.
intros b.
refine (match b with | nil _ => _ | cons _ _ _ _ => _ end).
  +
    reflexivity.
  +
    unfold IDProp.
    intros.
    apply H.
Qed.


Lemma rev_one : forall (x : R),
  rev [x] = [x].
Proof.
  intros x. 
  rewrite rev_cons. 
  rewrite rev_nil.
  simpl. 
  reflexivity.
Qed.


Lemma vec_nz_rev_nz : forall {n : nat} (a : vector n), check_nonzero a -> check_nonzero (rev a).
Proof.
  intros.
  unfold check_nonzero.
  rewrite Forall_rev.
  apply H.
Qed.


Lemma vec_nz_v_find_nz : forall {n : nat} (d : vector n), check_nonzero (v_find d) -> check_nonzero (d).
Proof.
intros n d H.
induction d.
-
  simpl in H. 
  constructor.
-
  simpl in H. 
  inversion H; 
  subst.
  constructor.
  +
    assumption.
  +
    apply IHd.
    apply Forall_cons_iff in H.
    destruct H.
    apply H0.
Qed.


Lemma vec_nonzero_hd_nz : forall {n : nat} (a : vector (S n)), check_nonzero a -> hd a <> 0.
Proof.
intros n a H.
rewrite vec_eq_hd_tl in H.
unfold check_nonzero in H.
apply Forall_cons_iff in H.
apply H.
Qed.

Lemma vec_nonzero_hd_nz' : forall {n : nat} (a : vector n) (b : R), check_nonzero (b :: a) -> b <> 0.
Proof.
  intros.
  unfold check_nonzero in H.
  apply Forall_cons_iff in H.
  apply H.
Qed.


Lemma vec_nz_tl_nz : forall {n : nat} (a : vector (S n)), check_nonzero a -> check_nonzero ((tl a)).
Proof.
  intros.
  rewrite vec_eq_hd_tl in H.
  unfold check_nonzero in H.
  apply Forall_cons_iff in H.
  apply H.
Qed.


Lemma vec_nz_tl_nz' : forall {n : nat} (a : vector n) (b : R), check_nonzero (b :: a) -> check_nonzero (a).
Proof.
  intros.
  unfold check_nonzero in H.
  apply Forall_cons_iff in H.
  apply H.
Qed.

Lemma vec_nz_tl_rev_nz : forall {n : nat} (a : vector (S n)), check_nonzero a -> check_nonzero ((tl (rev a))).
Proof.
intros n a H.
apply vec_nz_tl_nz.
apply vec_nz_rev_nz.
apply H.
Qed.


Lemma div_nz: forall (a b : R), (a / b) <> 0 -> a <> 0 /\ b <> 0.
Proof.
intros.
split.
  +
    intros Ha.
    rewrite Ha in H.
    unfold Rdiv in H. 
    rewrite Rmult_0_l in H.
    apply H.
    reflexivity.
  +
    intros Hb.
    unfold Rdiv in H.
    rewrite Hb in H.
    rewrite Rinv_0 in H.
    rewrite Rmult_0_r in H.
    apply H.
    reflexivity.
Qed.


Lemma no_brackets : forall (r1 r2 r3 : R),
  (r1 * r2 * / r3)%R = (r1 * (r2 * / r3))%R.
Proof.
  intros r1 r2 r3.
  apply Rmult_assoc.
Qed.


Lemma hd_eq_one_v : forall (b : vector 1), [hd b] = b.
Proof.
intros b.
rewrite vec_eq_hd_tl.
f_equal.
rewrite v0_eq_nil.
reflexivity.
Qed.


(* Корректность построенного разложения*)

Lemma LU'_cor : forall {n : nat} (a : vector (S n)) (d c : vector n) (v0 u0 : R), 
let v := v_find d in (check_nonzero d) /\ (check_nonzero (l' _ (find_LU' a v c u0))) ->
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
        replace (hd c * / q * hd d * q * / hd d) with (hd c).
          +++
            rewrite <- vec_eq_hd_tl.
            reflexivity.
          +++
            rewrite Rmult_assoc with (hd c) (/ q) (hd d).
            rewrite Rmult_comm with (hd c) ((/ q * hd d)).
            rewrite Rmult_comm.
            rewrite Rmult_comm with (/q) (hd d).

            rewrite <- Rmult_assoc.
            rewrite <- Rmult_assoc.
            rewrite <- Rmult_assoc.
            rewrite Rmult_comm with (/ hd d) (hd d).
            rewrite Rinv_r.
              ++++
                rewrite Rmult_1_l.
                rewrite Rmult_comm.
                rewrite <- Rmult_assoc.
                rewrite Rinv_r.
                  -
                    rewrite Rmult_1_l.
                    reflexivity.
                  -
                    unfold q.
                    destruct H.
                    apply vec_nonzero_hd_nz' in H0.
                    unfold li_find in H0.
                    apply div_nz in H0.
                    apply H0.
              ++++
                apply vec_nonzero_hd_nz.
                apply H.
      ++
        apply vec_nonzero_hd_nz.
        apply H.
      ++
        destruct H.
        split.
          -
            apply vec_nz_tl_nz.
            apply H.
          -
            apply vec_nz_tl_nz' in H0.
            apply H0.
Qed.


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
    rewrite Rmult_comm.
    rewrite <- Rmult_assoc.
    replace (hd d * hd a * / hd d) with (hd a).
    ++
      rewrite <- vec_eq_hd_tl.
      replace (hd a * / hd d * (hd c / (hd a * / hd d))) with (hd c).
      +++
        rewrite <- vec_eq_hd_tl.
        unfold mkA.
        simpl.
        reflexivity.
      +++
        unfold Rdiv.
        rewrite <- Rmult_assoc.
        rewrite Rinv_mult.
        rewrite Rinv_inv.
        unfold Rdiv.
        rewrite <- Rmult_assoc.
        rewrite Rmult_comm with ( hd a) ( /hd d).
        rewrite Rmult_comm.
        rewrite <- Rmult_assoc.
        rewrite <- Rmult_assoc.
        rewrite <- Rmult_assoc.
        rewrite Rmult_inv_m_id_r.
          ++++
            rewrite Rmult_inv_r_id_m.
            -
              reflexivity.
            -
              unfold is_consistent in H.
              unfold magicL in H.
              unfold make_L in H.
              simpl in H.
              unfold l1_find in H.
              destruct H.
              apply vec_nonzero_hd_nz' in H.
              apply div_nz in H.
              apply H.
          ++++
            unfold is_consistent in H.
            unfold magicL in H.
            unfold make_L in H.
            simpl in H.
            unfold l1_find in H.
            destruct H.
            apply vec_nonzero_hd_nz' in H.
            apply div_nz in H.
            apply H.
    ++
      rewrite Rmult_comm with (hd d) (hd a).
      rewrite Rinv_r_simpl_l with (hd d) (hd a).
        +++
          reflexivity.
        +++
            unfold is_consistent in H.
            unfold magicL in H.
            unfold make_L in H.
            simpl in H.
            unfold l1_find in H.
            destruct H.
            apply vec_nonzero_hd_nz' in H.
            apply div_nz in H.
            apply H.
    ++
      unfold is_consistent in H.
      destruct H.
      split.
        +++
          unfold magicU in H0.
          unfold make_U in H0.
          simpl in H0.
          apply vec_nz_tl_nz' in H0.
          apply vec_nz_v_find_nz in H0.
          apply H0.
        +++
          unfold magicL in H.
          unfold make_L in H.
          simpl in H.
          apply vec_nz_tl_nz' in H.
          apply H. 
Qed.


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

Lemma L_mul'_cor : forall {n : nat} (l' b : vector n) (y0 : R), check_nonzero l' ->
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
        apply vec_nonzero_hd_nz.
        apply H.
      ++
        apply vec_nz_tl_nz.
        apply H.
Qed.


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
    apply vec_nonzero_hd_nz.
    apply H.
  +
    unfold magicL in H.
    apply vec_nz_tl_nz.
    apply H.
Qed.


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


Definition find_x {n : nat} (U : U_matrix n) (y' : vector (S n)) : vector (S n) :=
  let u := rev (u _ U) in
  let v := rev (v _ U) in
  let y := rev y' in
  let vn := hd v in
  let yn := hd y in
  let initv := tl v in
  let inity := tl y in

  let xn := xn_find yn vn in

  rev(xn :: (find_x' inity u initv xn)).


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
  rev (yn :: (U_mul' initx initv u xn)).


(* Корректность найденного решения системы Ux = y *)

Lemma U_mul'_cor : forall {n : nat} (y u v : vector n) (x0 : R), check_nonzero v ->
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
        apply vec_nonzero_hd_nz.
        apply H.
      ++
        apply vec_nz_tl_nz.
        apply H.
Qed.


Lemma U_solution:
  forall {n : nat} (U : U_matrix n) (y : vector (S n)), magicU U -> (U_mul U ((find_x U y))) = y.
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
    rewrite rev_rev.
    reflexivity.
  +
    unfold magicU in H.
    simpl in H.
    apply vec_nonzero_hd_nz.
    apply vec_nz_rev_nz.
    apply H.
  +
    unfold magicU in H.
    simpl in H.
    apply vec_nz_tl_rev_nz.
    apply H.
Qed.


(* PART4 Доказательство корректности алгоритма *)

(* Умножение матриц Ax *)

Fixpoint matrix_mul' (n : nat) (a x : vector (S n)) (d c : vector n) (xi di : R) : vector (S n) :=
  match n return vector n -> vector (S n) -> vector (S n) -> vector n -> vector (S n) with
  | 0 => fun d a x c =>
    let d1 := di in
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
    let f2 := di * x1 in
    let f3 :=c1 * x2 in
    let f := f1 + f2 + f3 in
    f :: (matrix_mul' k tla tlx tld tlc x1 di)
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
    let d1 := hd (d'' _ SLE) in
    let tld := tl (d'' _ SLE) in
    let x1 := hd x in
    let tlx := tl x in
    let x2 := hd tlx in
    let f1 :=  (a1 * x1) + (c1 * x2) in
    f1 :: (matrix_mul' k tla tlx tld tlc x1 d1)
  end SLE x.


(* Ассоциативность умножения матриц *)
(* (L*U)*x = L (U * x) *)

Lemma target_lemma : forall {n : nat}  (l x v : vector (S (S n))) ( u : vector (S n)),
L_mul' (tl (tl l)) (tl (tl (U_mul {| v := v; u := u |} x)))
(hd (tl (U_mul {| v := v; u := u |} x))) =
tl
(matrix_mul' n (a'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (tl x)
(d'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u)))
(c'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (hd x) (hd v)).
Proof.
intros.
destruct n as [| k].
  +
    simpl.
    reflexivity.
  +
    (*  Выглядит разумно попробовать переписать это как ручками:
        обозначить штуки с U_mul как u[i], аналогично в IHn,
        и пытаться работать с этим как с человеческим выражением.

        ОТДЕЛЬНО:

        Для переписывания в IHn доказать что-нибудь в духе:
        При удленении вектора любым элементом - ничего не меняется для конкретных tl (tl (...))
        
     *)

      generalize dependent x.
      induction k as [| k' IHk].
        ++
          intros x.
          simpl.
          unfold U_mul.
          simpl.
          admit.
        ++
          intros x.
          rewrite vec_eq_hd_tl with (x).
          set (x1 := hd x).
          set (tlx := tl x).
          simpl.
          specialize (IHk tlx).


          admit.

      
    


Admitted.


Lemma Revvv : forall  (a b : R) , hd (rev [a ; b]) = b.
Proof.
intros.
Admitted.

Lemma Revv : forall {n : nat} (a b : R) (U : vector (S n)), hd (rev (a :: b :: U)) = hd (rev U).
Proof.
intros.
Admitted.

Lemma Revvvv : forall {n : nat} (a : vector (S(S n))) , hd (tl (rev a)) = hd a.
Proof.
intros.
Admitted.


(* Нужна общая лемма, в духе: (ai : R) (b : vector n), hd (rev (a1 :: a2 :: ... :: an :: b)) = hd (rev b) *)


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
  rewrite hd_eq_one_v.
  rewrite <- hd_eq_one_v with (x).
  rewrite rev_one.
  reflexivity.
+
  simpl.
  destruct L as [l].
  destruct U as [v u].
  simpl.
  rewrite vec_eq_hd_tl.
  unfold matrix_mul, L_mul in IHn.
  unfold L_mul.
  simpl.
  unfold U_mul at 1.
  simpl.
  rewrite Revvvv.
  rewrite Revvvv.
  set (q := hd l * hd v * hd x + hd l * hd u * hd (tl x)).
  replace (hd l * hd (rev (hd (rev v) * hd (rev x) :: hd v * hd x + hd (rev u) * hd (rev x) :: U_mul' (tl (tl (rev x))) (tl (tl (rev v))) (tl (rev u)) (hd x)))) with q.
    ++
      replace ( matrix_mul' n (a'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (tl x)
            (d'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u)))
            (c'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (hd x) (hd v)) with (hd (U_mul {| v := v; u := u |} x) + hd (tl l) * hd (tl (U_mul {| v := v; u := u |}
            x))
            :: L_mul' (tl (tl l)) (tl (tl (U_mul {| v := v; u := u |} x)))
            (hd (tl (U_mul {| v := v; u := u |} x)))).
        +++
          reflexivity.
        +++
          rewrite vec_eq_hd_tl.
          replace (hd (matrix_mul' n (a'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (tl x) (d'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (c'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (hd x) (hd v))) with (hd (U_mul {| v := v; u := u |} x) + hd (tl l) * hd (tl (U_mul {| v := v; u := u |} x))).
            ++++
              set (s := hd (U_mul {| v := v; u := u |} x) + hd (tl l) * hd (tl (U_mul {| v := v; u := u |} x))).
              replace (tl (matrix_mul' n (a'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (tl x) (d'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (c'' n (LU_mul' (tl v) (tl l) (tl u) (hd v) (hd u))) (hd x) (hd v))) with (L_mul' (tl (tl l)) (tl (tl (U_mul {| v := v; u := u |} x))) (hd (tl (U_mul {| v := v; u := u |} x)))).
                -
                  reflexivity.
                -
                  rewrite target_lemma.
                  reflexivity.
            ++++
              rewrite vec_eq_hd_tl with (x).
              set (x1 := hd x).
              set (tlx := tl x).
              simpl.

              (* РУЧКАМИ *)
              admit.
    ++

      (* ТОЧНО РУЧКАМИ *)
      admit.
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
