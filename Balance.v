(*
This proof script is tested with   
- The Coq Proof Assistant, version 8.2pl1 (July 2010) 
- CSDP 6.0.1
*)


(*************************************************
   Part 1: arithmetic lemmas parametrized with
   balance condition and single/double condition.
*************************************************)
Section general.
  
Require Import Bool.
Require Import QArith.
Require Import Psatz.

Open Scope Q_scope.

Lemma Qmult_le_compat_l:
  forall x y z: Q, x <= y -> 0 <= z -> z*x <= z*y.
  intros x y z.
  psatz Q.
Qed.
  
Variable isBalancedSizeQ: Q -> Q -> Prop.
Variable isSingleSizeQ: Q -> Q -> bool.

Definition balanced_emptyQ:= (isBalancedSizeQ (0#1) (0#1)).

Definition balancedQ (l r:Q) :=
  l >= 0 /\ r >= 0 /\ isBalancedSizeQ l r /\ isBalancedSizeQ r l.

Definition singly_balanced (a c d e: Q) :=
  balancedQ a (c + d + 1) /\
  balancedQ c d /\
  balancedQ (a + c + d + 1 + 1) e.

Definition doubly_balanced (a c d e: Q) :=
  balancedQ a c /\
  balancedQ d e /\
  balancedQ (a + c + 1) (d + e + 1).

Definition deep_insert_single (a b c d e: Q) :=
  balancedQ a b ->
  ~balancedQ a (b + 1) ->
  c + d + 1 + e + 1 == b + 1 ->
  balancedQ c d ->
  balancedQ (c + d + 1) e ->
  if (isSingleSizeQ (c + d + 1) e) 
    then 
      singly_balanced a c d e
    else True.

Definition deep_insert_double (a b c d e: Q) :=
  balancedQ a b ->
  ~balancedQ a (b + 1) ->
  c + d + 1 + e + 1 == b + 1 ->
  balancedQ c d ->
  balancedQ (c + d + 1) e ->
  if (isSingleSizeQ (c + d + 1) e) 
    then 
      True
    else doubly_balanced a c d e.

Definition deep_insert (a b c d e: Q) :=
  balancedQ a b ->
  ~balancedQ a (b + 1) ->
  c + d + 1 + e + 1 == b + 1 ->
  balancedQ c d ->
  balancedQ (c + d + 1) e ->
  if (isSingleSizeQ (c + d + 1) e) 
    then 
      singly_balanced a c d e
    else doubly_balanced a c d e.

Definition deep_delete (a b c d e: Q) :=
    0 <= a ->
    balancedQ (1 + a) b ->
    ~balancedQ a b ->
    c + d + 1 + e + 1 == b ->
    balancedQ c d ->
    balancedQ (c + d + 1) e ->
    if (isSingleSizeQ (c + d + 1) e) then 
      singly_balanced a c d e
      else 
        doubly_balanced a c d e.

Definition shallow_singly_balanced (a e: Q) :=
  balancedQ a 0 /\
  balancedQ (a + 1) e.

Definition shallow_insert (a e: Q) :=
  balancedQ a e ->
  balancedQ 0 e ->
  ~balancedQ a (e + 1) ->
  Is_true (isSingleSizeQ 0 e) /\
  shallow_singly_balanced a e.

Definition shallow_delete (a e: Q) :=
    0 <= a ->
    balancedQ (1 + a) (1 + e) ->
    balancedQ 0 e ->
    ~balancedQ a (1 + e) ->
    Is_true (isSingleSizeQ 0 e) /\
    shallow_singly_balanced a e.

End general.

(*
   We fix the parameter pair here.
*)

Axiom delta : Q.
Axiom ratio : Q.

Open Scope Q_scope.


(*
   for soundness proof, we assume that the parameter pair is inside the range
*)

Definition normal :=
  0 <= (delta - 1) /\ (delta - 1) ^ 2 >= (2 # 1) /\ ratio > 1.

Definition slope :=
 ratio <= delta - 1.

Definition curve:=
delta + 1 <= delta * ratio.


Definition deltasup:= delta < (9#2).

Definition ceilA:=
  (5#2) <= delta  -> delta < (3#1) -> ratio <= (3#2).

Definition ceilB:=
  (3#1) <= delta -> delta < (7#2) -> ratio <= (2#1).

Definition ceilC:=
  (7#2) <= delta -> delta < (4#1) -> ratio <= (4#3).

Definition ceilD:=
  (4#1) <= delta -> delta < (9#2) -> ratio <= (5#3).

Definition good_params :=
  normal /\ slope /\ curve /\ deltasup /\ ceilA /\ ceilB /\ ceilC /\ ceilD.

(*
   We define isBalancedSize and isSingleSize functions using the parameter pair
*)

Definition isBalancedSize (x y:Q): Prop :=
  delta * (x + 1) >= (y + 1).

Require Import Arith.Compare_dec.

Definition Qlt_le_dec_bool (x y:Q): bool :=
  if Qlt_le_dec x y then true else false.

Infix "'<'" := Qlt_le_dec_bool (at level 50).

Definition isSingleSize (x y:Q): bool :=
  if (1 + x) '<' (ratio * (1 +y)) then true else false.

Definition isSingleSizeP (x y: Q): Prop :=
  1 + x < ratio * (1 + y).

Lemma isSingleSizeP_aux:
  forall (x y: Q),
    isSingleSizeP x y <-> Is_true (isSingleSize x y).
  intros x y.
  split.
  unfold isSingleSize.
  unfold Qlt_le_dec_bool.
  unfold isSingleSizeP.
  intro lt.
  case (Qlt_le_dec (1 + x) (ratio * (1 + y))).
  intuition.
  intro.
  compute.
  psatzl Q.
  
  unfold isSingleSize.
  unfold Qlt_le_dec_bool.
  case (Qlt_le_dec (1 + x) (ratio * (1 + y))).
  unfold isSingleSizeP.
  intuition.
  unfold Is_true.
  intuition.
  Qed.
  

Require Import Omega.

(* proving the arithmetic lemmas *)

Lemma le_sqrt_compat:
  forall (x y: Q),
    0 <= y -> x ^ 2 <= y ^ 2 -> x <= y.
  intros x y.
  intros ypos.
  case (Qlt_le_dec y x).
  intro ylex.
  psatz Q.
  psatz Q.
  Qed.

Lemma delta_two:
  normal -> delta >= (2 # 1).
  unfold normal.
  psatz Q.
  Qed.

Lemma delta_pos:
  normal -> delta > 0.
  intro s.
  apply Qlt_le_trans with (1 + 1).
  intuition.
  apply delta_two.
  auto.
  Qed.


Lemma delta_nonneg:
  normal -> delta >= 0.
  intro s.
  apply Qle_trans with (2 # 1).
  intuition.
  apply delta_two.
  auto.
  Qed.

Lemma NR_deep_insert_single:
  good_params -> forall (a b c d e: Z),
  deep_insert_single isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1).
  compute [good_params].
  compute [normal slope curve deltasup ceilA ceilB ceilC ceilD].
  intro g_params.
  intros a b c d e.
  compute [balancedQ doubly_balanced singly_balanced deep_insert_single
    isBalancedSize isSingleSize negb good_params].
  unfold Qlt_le_dec_bool.
  case_eq (Qlt_le_dec (1 + ((c # 1) + (d # 1) + 1)) (ratio * (1 + (e # 1)))).
  intro ratio_compare.
  intuition.
  clear H.
  psatzl Q.
  Focus 2.
  clear - H7 H0 H8.
  psatzl Q.
  Unfocus.
  Focus 2.
  clear H.
  psatzl Q.
  Unfocus.
  assert ((b # 1) + 1 + 1 <= delta * ((a # 1) + 1) /\
    (a # 1) + 1 <= delta * ((b # 1) + 1 + 1) -> False).
  apply H23.
  apply Qle_trans with (b # 1).
  assumption.
  eapply Qle_minus_iff; ring_simplify; intuition.
  clear H22.
  assert
    ((a # 1) + 1 <= delta * ((b # 1) + 1 + 1)).
  apply Qle_trans with (delta * ((b # 1) + 1)).
  assumption.
  apply Qmult_le_compat_l.
  eapply Qle_minus_iff; ring_simplify; intuition.
  apply delta_nonneg; compute [normal]; intuition.
  assert 
    (delta * ((a # 1) + 1) < (b # 1) + 1 + 1).
  generalize Qlt_le_dec.
  intro Qdec.
  elim Qdec with (delta * ((a # 1) + 1)) ((b # 1) + 1 +1).
  clear Qdec.
  auto.
  intro le.
  apply False_ind.
  apply H1.
  split.
  auto.
  auto.
  clear H.
  clear H1.
  apply Qle_trans with (((b # 1) + 1 + 1) / delta).
  eapply Qle_shift_div_l.
  apply delta_pos; compute [normal]; intuition.
  rewrite Qmult_comm; apply Qlt_le_weak; assumption.
  apply Qle_shift_div_r.
  apply delta_pos; compute[normal]; intuition.
  rewrite <- H2.
  apply Qle_trans with (((c # 1) + (d # 1) + 1 + 1)+ delta * ((c # 1) + (d # 1) + 1 + 1)).
  clear - H14.
  apply Qle_trans with ((c # 1) + (d # 1) + 1 + 1 + ((e # 1) + 1)).
  eapply Qle_minus_iff.
  ring_simplify.
  intuition.
  apply Qle_trans with (   (c # 1) + (d # 1) + 1 + 1 + (delta * ((c # 1) + (d # 1) + 1 + 1))).
  apply Qplus_le_compat.
  intuition.
  assumption.
  intuition.
  generalize dependent ((c # 1) + (d # 1) + 1 + 1).
  intro q.
  intro one.
  intro two.
  eapply Qle_minus_iff.
  apply Qle_trans with ((delta * delta - delta - 1) * q).
  apply Qmult_le_0_compat.
  apply Qle_trans with (delta * delta - (1 + 1) * delta + 1).
  apply Qle_trans with ((delta - 1) * (delta - 1)).
  apply Qmult_le_0_compat.
  generalize Qle_minus_iff; intro qle; elim qle with 1 delta.
  intro qle1.
  intro irr.
  clear irr.
  apply qle1.
  clear qle1.
  clear qle.
  apply Qle_trans with (1+1).
  intuition.
  apply delta_two; compute [normal]; intuition.
  generalize Qle_minus_iff.
  intro qle.
  elim qle with 1 delta.
  intro qle1.
  intro irr.
  clear irr.
  apply qle1.
  clear qle1.
  clear qle.
  apply Qle_trans with (1+1).
  intuition.
  apply delta_two; compute [normal]; intuition.
  eapply Qle_minus_iff; ring_simplify; intuition.
  eapply Qle_minus_iff; ring_simplify.
  apply Qle_trans with ((1 + 1) + (-2 # 1)).
  intuition.
  apply Qplus_le_compat.
  apply delta_two.
  compute [normal]; intuition.
  intuition.
  apply Qle_trans with (((e#1) + 1) / delta).
  apply Qle_shift_div_l.
  apply delta_pos.
  compute[normal]; intuition.
  ring_simplify.
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  auto.
  intuition.
  apply Qle_shift_div_r.
  apply delta_pos; compute [normal]; intuition.
  rewrite Qmult_comm.
  auto.
  eapply Qle_minus_iff; ring_simplify; compute; discriminate.
  assert (
    (b # 1) + 1 + 1 <= delta * ((a # 1) + 1) /\
    (a # 1) + 1 <= delta * ((b # 1) + 1 + 1) -> False
  ).
  apply H23.
  apply Qle_trans with (b # 1).
  assumption.
  eapply Qle_minus_iff; ring_simplify ; intuition.
  clear H22.
  assert 
    ((b # 1) + 1 + 1 > delta * ((a # 1) + 1)).
  case_eq (Qlt_le_dec (delta * ((a # 1) + 1))
    ((b # 1) + 1 + 1)).
  intro q.
  intro dec.
  clear dec.
  auto.
  intro q.
  intro dec.
  clear dec.
  apply False_ind.
  apply H1.
  split.
  auto.
  clear q.
  apply Qle_trans with (delta * ((b # 1) + 1)).
  assumption.
  eapply Qle_minus_iff; ring_simplify.
  apply delta_nonneg; compute [normal]; intuition.
  apply Qle_trans with (((b # 1) + 1 + 1) / delta + (c # 1) + (d # 1) + 1 + 1).
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  rewrite Qplus_comm.
  rewrite Qplus_assoc.
  apply Qplus_le_compat.
  rewrite Qplus_assoc.
  apply Qplus_le_compat.
  apply Qlt_le_weak.
  apply Qlt_shift_div_l.
  apply delta_pos; compute [normal]; intuition.
  rewrite Qmult_comm.
  rewrite Qplus_comm.
  auto.
  intuition.
  intuition.
  intuition.
  intuition.
  clear H1.
  rewrite <- H2.
  apply Qle_trans with
    (((e # 1) + (1 + ratio * (1 + (e # 1)))) / delta + ratio * (1 + (e # 1))).
  clear H7 H0 H12 H H17.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + (e # 1) + 1 + 1) / delta + ((c # 1) + (d # 1) + 1 + 1)).
  eapply Qle_minus_iff; ring_simplify; intuition.
  apply Qplus_le_compat.
  apply Qle_shift_div_r.
  apply delta_pos; compute[normal]; auto.
  apply Qle_trans with (ratio * (1 + (e # 1)) + (e # 1) + 1).
  apply Qle_trans with ((c # 1) + (d # 1) + 1 + 1 + (e # 1) + 1).
  ring_simplify.
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  apply Qle_trans with (1 + ((c # 1) + (d # 1) + 1)).
  eapply Qle_minus_iff; ring_simplify; intuition.
  apply Qlt_le_weak.
  auto.
  intuition.
  intuition.
  apply Qle_trans with (delta * (((e # 1) + (1 + ratio * (1 + (e # 1)))) / delta)).
  rewrite Qmult_div_r.
  eapply Qle_minus_iff; ring_simplify; intuition.
  intro.
  rewrite H in H4.
  generalize H4.
  compute.
  intro s.
  apply s.
  auto.
  rewrite Qmult_comm.
  intuition.
  apply Qle_trans with (1 + ((c # 1) + (d # 1) + 1)).
  eapply Qle_minus_iff; ring_simplify; intuition.
  apply Qlt_le_weak.
  auto.
  apply Qle_trans with ((((e # 1) + 1) + ratio * ((e # 1) + 1)) / delta + ratio * ((e # 1) + 1)).
  apply Qplus_le_compat.
  apply Qle_shift_div_r.
  apply delta_pos.
  compute [normal].
  auto.
  field_simplify.
  intuition.
  intro eq.
  rewrite eq in H4.
  generalize H4.
  compute.
  intro neq.
  apply neq.
  auto.
  rewrite Qplus_comm.
  intuition.
  apply Qle_trans with
    (((e # 1) + 1 + (delta - 1) * ((e # 1) + 1)) / delta + (delta - 1) * ((e # 1) + 1)).
  apply Qplus_le_compat.
  apply Qle_shift_div_r.
  apply delta_pos; compute [normal]; intuition.
  Focus.
  apply Qle_trans with (delta * (((e # 1) + 1 + (delta - 1) * ((e # 1) + 1)) / delta)).
  rewrite Qmult_div_r.
  apply Qplus_le_compat.
  intuition.
  apply Qmult_le_compat_r.
  auto.
  apply Qle_trans with (e # 1).
  auto.
  eapply Qle_minus_iff; ring_simplify; intuition.
  Focus.
  intro eq.
  rewrite eq in H4.
  generalize H4.
  compute.
  intuition.
  Unfocus.
  rewrite Qmult_comm.
  intuition.
  Focus.
  apply Qmult_le_compat_r.
  auto.
  apply Qle_trans with (e # 1).
  auto.
  eapply Qle_minus_iff; ring_simplify; intuition.
  Unfocus.
  assert (0 <= (e # 1) + 1).
  apply Qle_trans with (e # 1).
  auto.
  eapply Qle_minus_iff; ring_simplify; intuition.
  generalize H1.
  generalize ((e # 1) + 1).
  intro q.
  intro qpos.
  apply Qle_trans with (((1 + (delta - 1)) / delta + (delta - 1)) * q).
  eapply Qle_minus_iff; field_simplify.
  compute. discriminate.
  intro zero.
  rewrite zero in H4.
  generalize H4.
  intuition.
  eapply Qle_minus_iff.
  field_simplify.
  compute.
  discriminate.
  intro zero.
  rewrite zero in H4; generalize H4; compute. intuition.
  auto.
  Qed.


Lemma NR_deep_insert_double:
  good_params -> forall (a b c d e: Z),
  deep_insert_double isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1).
  unfold good_params.
  unfold normal, slope, curve, deltasup, ceilA, ceilB, ceilC, ceilD, deep_insert_double.
  compute [balancedQ isSingleSize isBalancedSize doubly_balanced].
  unfold Qlt_le_dec_bool.
  intro pre.
  intros a b c d e.
  case_eq (Qlt_le_dec (1 + ((c # 1) + (d # 1) + 1)) (ratio * (1 + (e # 1)))).
  auto.
  intuition.
  apply Qle_trans with ((b # 1) + 1).
  rewrite <- H12.
  eapply Qle_minus_iff.
  ring_simplify.
  apply Qle_trans with (0 + 0 + 0).
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  auto.
  auto.
  intuition.
  auto.
  Focus 3.
  apply Qle_trans with ((c # 1) + (d # 1) + 1 + 1).
  eapply Qle_minus_iff; ring_simplify.
  apply Qle_trans with (c # 1).
  auto.
  eapply Qle_minus_iff; ring_simplify; intuition.
  auto.
  Unfocus.
  Focus 3.
  apply Qle_trans with (0 + 0 + 0).
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  auto.
  auto.
  intuition.
  Unfocus.
  Focus 3.
  apply Qle_trans with (0 + 0 + 0).
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  auto.
  auto.
  intuition.
  Unfocus.
  Focus 3.
  apply Qle_trans with ((b # 1) + 1).
  rewrite <- H12.
  eapply Qle_minus_iff.
  ring_simplify.
  auto.
  apply Qle_trans with (delta * ((a # 1) + 1)).
  auto.
  apply Qmult_le_compat_l.
  eapply Qle_minus_iff.
  ring_simplify.
  apply Qle_trans with (c # 1).
  auto.
  eapply Qle_minus_iff.
  ring_simplify.
  intuition.
  apply delta_nonneg; compute [normal]; intuition.
  Unfocus.
  assert (delta * ((a # 1) + 1) < (b # 1) + 1 + 1).
  case (Qlt_le_dec (delta * ((a # 1) + 1)) ((b # 1) + 1 + 1)).
  auto.
  intro f.
  apply False_ind.
  apply H21.
  apply Qle_trans with (b # 1).
  auto.
  eapply Qle_minus_iff.
  ring_simplify.
  intuition.
  split.
  auto.
  apply Qle_trans with (delta * ((b # 1) + 1)).
  auto.
  apply Qmult_le_compat_l.
  eapply Qle_minus_iff.
  ring_simplify.
  intuition.
  apply delta_nonneg; compute[normal]; intuition.
  apply Qle_trans with (((b # 1) + 1 + 1) / delta).
  Focus.
  apply Qle_shift_div_l.
  apply delta_pos; compute [normal]; intuition.
  apply Qlt_le_weak.
  rewrite Qmult_comm.
  auto.
  Unfocus.
  rewrite <- H12.
  apply Qle_shift_div_r.
  apply delta_pos; compute [normal]; intuition.
  clear H7.
  apply Qle_trans with
    ((c # 1) + (d # 1) + 1 + 1 + ((1 + ((c # 1) + (d # 1) + 1)) / ratio)).
  apply Qle_trans with (((c # 1) + (d # 1) + 1 + 1) + ((e # 1) + 1)).
  ring_simplify.
  intuition.
  apply Qplus_le_compat.
  intuition.
  rewrite Qplus_comm.
  apply Qle_shift_div_l.
  apply Qlt_trans with 1.
  intuition.
  auto.
  rewrite Qmult_comm.
  auto.
  apply Qle_trans with
    ((c # 1) + delta * ((c # 1) + 1) + 1 + (1 + ((c # 1) + delta * ((c # 1) + 1))) / ratio).
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat.
  intuition.
  auto.
  intuition.
  apply Qle_shift_div_l.
  apply Qlt_trans with 1.
  intuition.
  auto.
  apply Qle_trans with (1 + ((c # 1) + (d # 1) + 1)).
  eapply Qle_minus_iff.
  field_simplify.
  intuition.
  clear - H4.
  intro eq.
  rewrite eq in H4.
  clear eq.
  generalize H4.
  compute.
  discriminate.
  Focus.
  apply Qplus_le_compat.
  intuition.
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat.
  intuition.
  auto.
  Unfocus.
  clear H.
  apply Qle_trans with
    ((c # 1) + delta * ((c # 1) + 1) + 1 +
      (1 + ((c # 1) + delta * ((c # 1) + 1))) / ((delta + 1) / delta)).
  apply Qplus_le_compat.
  intuition.
  apply Qmult_le_compat_l.
  apply Qle_shift_inv_l.
  apply Qlt_shift_div_l.
  apply delta_pos.
  compute [normal].
  auto.
  apply Qlt_trans with 1.
  intuition.
  apply Qlt_trans with delta.
  apply Qlt_le_trans with (1 + 1).
  intuition.
  apply delta_two.
  compute [normal]; auto.
  eapply Qlt_minus_iff.
  ring_simplify.
  intuition.
  rewrite Qmult_comm.
  apply Qle_shift_div_r.
  apply Qlt_trans with 1.
  intuition.
  auto.
  apply Qle_trans with ratio.
  auto.
  ring_simplify.
  intuition.
  Focus 3.
  apply Qle_trans with (0 + (0 + 0)).
  intuition.
  apply Qplus_le_compat.
  intuition.
  apply Qplus_le_compat.
  auto.
  apply Qmult_le_0_compat.
  apply delta_nonneg; compute [normal]; intuition.
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  auto.
  intuition.
  Unfocus.
  Focus 3.
  apply Qle_trans with
    (((c # 1) + 1) + delta * ((c # 1) + 1) +
   (((c # 1) + 1) + (delta * ((c # 1) + 1))) / ((delta + 1) / delta)).
  eapply Qle_minus_iff.
  field_simplify.
  intuition.
  clear -H1.
  split.
  intro eq.
  rewrite eq in H1.
  generalize H1.
  intuition.
  intro peq.
  assert (delta == 0 - 1).
  assert (delta + 1 - 1 == 0 - 1).
  rewrite peq.
  intuition.
  clear peq.
  ring_simplify in H.
  ring_simplify.
  apply H.
  clear peq.
  rewrite H in H1.
  generalize H1.
  compute.
  auto.
  assert (0 <= ((c # 1) + 1)).
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  auto.
  intuition.
  generalize H.
  clear H.
  generalize ((c # 1) + 1).
  intro x.
  intro xpos.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  apply Qlt_trans with delta.
  apply delta_pos.
  unfold normal.
  auto.
  eapply Qlt_minus_iff.
  ring_simplify.
  intuition.
  field_simplify.
  apply Qle_trans with
    ((delta ^ 3 + (-1 # 1) * delta ^ 2 + (-3 # 1) * delta +
    (-1 # 1)) * x).
  apply Qmult_le_0_compat.
  Focus 2.
  assumption.
  Unfocus.
  clear - H2 H1.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  clear xpos.
  Focus 2.
  eapply Qle_minus_iff.
  field_simplify.
  intuition.
  Unfocus.
  Focus 2.
  intuition.
  rewrite H in H1.
  generalize H1.
  intuition.
  assert (delta + 1 <= delta - 1).
  rewrite H.
  auto.
  apply Qle_not_lt in H0.
  apply H0.
  eapply Qlt_minus_iff.
  ring_simplify.
  intuition.
  Unfocus.
  Focus.
  apply Qle_trans with ((delta + 1) * (delta ^ 2 - (1 + 1) * delta - 1)).
  apply Qmult_le_0_compat.
  auto.
  apply Qle_trans with (0 + 1).
  intuition.
  apply Qplus_le_compat.
  apply delta_nonneg.
  compute [normal].
  auto.
  intuition.
  apply Qle_trans with ((delta ^ 2 - (1 + 1) * delta + 1) - (2 # 1)).
  apply Qle_trans with ((delta - 1) ^ 2 - (2 # 1)).
  eapply Qle_minus_iff in H0.
  exact H0.
  eapply Qle_minus_iff.
  ring_simplify.
  intuition.
  ring_simplify.
  intuition.
  ring_simplify.
  intuition.
  Unfocus.
  Focus.
  psatzl Q.
  Unfocus.
  Focus.
  apply Qle_trans with
    ((1 + ((c # 1) + (d # 1) + 1)) / ratio).
  apply Qle_shift_div_l.
  apply Qlt_trans with 1.
  intuition.
  auto.
  rewrite Qmult_comm.
  rewrite Qplus_comm.
  auto.
  apply Qle_shift_div_r.
  apply Qlt_trans with 1.
  intuition.
  auto.
  apply Qle_trans with
    (1 + ((delta * ((d # 1) + 1)) + (d # 1))).
  apply Qplus_le_compat.
  intuition.
  rewrite Qplus_comm.
  rewrite Qplus_assoc.
  apply Qplus_le_compat.
  rewrite Qplus_comm.
  auto.
  intuition.
  apply Qle_trans with
    (delta * ((d # 1) + 1) * ((delta + 1) / delta)).
  eapply Qle_minus_iff.
  field_simplify.
  intuition.
  intro eq.
  rewrite eq in H1.
  generalize H1.
  compute.
  auto.
  apply Qmult_le_compat_l.
  clear - H1 H2.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  apply Qmult_le_0_compat.
  apply delta_nonneg; compute [normal]; auto.
  apply Qle_trans with 1.
  intuition.
  eapply Qle_minus_iff.
  ring_simplify.
  auto.
  Unfocus.
  assert (
    delta * ((a # 1) + 1) < (b # 1) + 1 + 1).
  case_eq (Qlt_le_dec
    (delta * ((a # 1) + 1)) ((b # 1) + 1 + 1)).
  intro x.
  intro y.
  clear y.
  exact x.
  intro x.
  intro y.
  clear y.
  apply False_ind.
  apply H21.
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  auto.
  intuition.
  split.
  exact x.
  clear x.
  apply Qle_trans with
    (delta * ((b # 1) + 1)).
  auto.
  eapply Qle_minus_iff.
  ring_simplify.
  apply delta_nonneg; compute [normal]; intuition.
  Focus.
  clear H21.
  apply Qle_trans with
    ((((b # 1) + 1 + 1) / delta) + (c # 1) + 1).
  apply Qplus_le_compat.
  rewrite Qplus_comm.
  rewrite Qplus_assoc.
  apply Qplus_le_compat.
  apply Qle_shift_div_l.
  apply delta_pos.
  compute [normal].
  auto.
  rewrite Qmult_comm.
  rewrite Qplus_comm.
  apply Qlt_le_weak.
  auto.
  intuition.
  intuition.
  Focus.
  rewrite <- H12.
  clear H11.
  clear H5.
  clear H6.
  clear H7.
  clear H8.
  clear H9.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + (e # 1) + 1 + 1) / delta + delta * ((d # 1) + 1)).
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat.
  intuition.
  auto.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + ((1 + ((c # 1) + (d # 1) + 1)) / ratio) + 1) / delta + delta * ((d # 1) + 1)).
  apply Qplus_le_compat.
  apply Qmult_le_compat_r.
  apply Qplus_le_compat.
  rewrite <- Qplus_assoc.
  apply Qplus_le_compat.
  intuition.
  apply Qle_shift_div_l.
  apply Qlt_trans with 1.
  intuition.
  auto.
  rewrite Qmult_comm.
  rewrite Qplus_comm.
  auto.
  intuition.
  apply Qle_shift_inv_l.
  apply delta_pos.
  unfold normal.
  auto.
  ring_simplify.
  intuition.
  intuition.
  Focus.
  apply Qle_trans with
    ((c # 1) + (d # 1) + 1 + 1 + delta * ((d # 1) + 1)).
  apply Qplus_le_compat.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + 1 + ((1 + ((c # 1) + (d # 1) + 1)) / ((delta + 1) / delta))) / delta).
  apply Qle_trans with
    ((((c # 1) + (d # 1) + 1 + 1 ) + (1 + ((c # 1) + (d # 1) + 1)) / ((delta + 1) / delta)) / delta).
  Focus 3.
  assert (1 <= ((c # 1) + (d # 1) + 1)).
  apply Qle_trans with (0 + 0 + 1).
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  auto.
  auto.
  intuition.
  Focus.
  generalize H5.
  generalize ((c # 1) + (d # 1) + 1).
  intro x.
  intro x_one.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  Focus 2.
  field_simplify.
  apply Qle_trans with
    ((x + 1) * (delta ^ 2 + (-1 # 1) * delta + (-1 # 1))).
  apply Qmult_le_0_compat.
  apply Qle_trans with (1 + 1).
  intuition.
  apply Qplus_le_compat.
  auto.
  intuition.
  apply Qle_trans with ((delta - 1) ^ 2).
  apply Qle_trans with ((delta - 1) * 0).
  ring_simplify.
  intuition.
  apply Qmult_le_compat_l.
  auto.
  auto.
  eapply Qle_minus_iff.
  ring_simplify.
  assert (delta >= (2 # 1)).
  apply delta_two.
  compute [normal].
  auto.
  apply Qle_trans with ((2 # 1) + (-2 # 1)).
  intuition.
  apply Qplus_le_compat.
  auto.
  intuition.
  eapply Qle_minus_iff.
  field_simplify.
  intuition.
  Unfocus.
  Focus.
  apply Qle_shift_div_l.
  apply delta_pos.
  unfold normal.
  auto.
  apply Qle_trans with
    ((c # 1) + (d # 1) + 1 + (1 + ((c # 1) + (d # 1) + 1)) / ratio + 1).
  field_simplify.
  intuition.
  clear - H4.
  intro eq.
  rewrite eq in H4.
  generalize H4.
  compute.
  discriminate.
  split.
  clear - H4.
  intro eq.
  rewrite eq in H4.
  generalize H4.
  compute.
  discriminate.
  assert (delta > 0).
  apply delta_pos.
  unfold normal.
  auto.
  clear - H5.
  intro eq.
  rewrite eq in H5.
  generalize H5.
  compute.
  discriminate.
  apply Qle_trans with
    ((c # 1) + (d # 1) + 1 + 1 + (1 + ((c # 1) + (d # 1) + 1)) / ratio).
  ring_simplify.
  intuition.
  apply Qplus_le_compat.
  intuition.
  apply Qmult_le_compat_l.
  apply Qle_shift_inv_l.
  apply Qlt_shift_div_l.
  apply delta_pos.
  unfold normal.
  auto.
  ring_simplify.
  apply Qlt_trans with 1.
  intuition.
  clear - H1.
  psatz Q.
  rewrite Qmult_comm.
  apply Qle_shift_div_r.
  clear - H4.
  psatz Q.
  ring_simplify.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with (0 + (0 + 0 + 0)).
  psatzl Q.
  psatzl Q.
  Unfocus.
  intuition.
  clear - H1.
  psatz Q.
  psatz Q.
  intuition.
  clear - H1 H24.
  psatz Q.
  Qed.


Lemma NR_deep_insert_in:
  forall (a b c d e: Z), 
  deep_insert_single isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1) -> 
  deep_insert_double isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1) ->
  deep_insert isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1).
  unfold deep_insert.
  intros a b c d e.
  case_eq (isSingleSize ((c # 1) + (d # 1) + 1) (e # 1)).
  compute [deep_insert_single].
  intuition.
  rewrite H in H7.
  auto.
  compute [deep_insert_double].
  intuition.
  rewrite H in H7.
  auto.
  Qed.


Lemma NR_deep_insert:
  good_params -> forall (a b c d e: Z),
  deep_insert isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1).
  intro gp.
  intros a b c d e.
  apply NR_deep_insert_in.
  apply NR_deep_insert_single.
  auto.
  apply NR_deep_insert_double.
  auto.
  Qed.

Lemma NR_deep_delete:
  good_params -> forall (a b c d e: Z),
  deep_delete isBalancedSize isSingleSize (a#1) (b#1) (c#1) (d#1) (e#1).
  unfold good_params.
  unfold normal, slope, curve, deltasup, ceilA, ceilB, ceilC, ceilD.
  intro gp.
  intros a b c d e.
  unfold deep_delete.
  compute [isSingleSize].
  unfold Qlt_le_dec_bool.
  case_eq (Qlt_le_dec (1 + ((c # 1) + (d # 1) + 1)) (ratio * (1 + (e # 1)))).
  intro lt.
  intro cl.
  clear cl.
  compute [balancedQ isSingleSize isBalancedSize singly_balanced].
  unfold Qlt_le_dec_bool.
  intuition.
  Focus 3.
  clear - H H0 H8.
  psatz Q.
  Unfocus.
  Focus 5.
  intro le.
  intro cl.
  clear cl.
  compute [balancedQ isBalancedSize isSingleSize doubly_balanced].
  unfold Qlt_le_dec_bool.
  intuition.
  Focus 5.
  clear - H H0.
  psatz Q.
  Unfocus.
  Focus 9.
  clear - H8 H9.
  psatz Q.
  Unfocus.
  Focus 3.
  clear - H14 H H4.
  psatz Q.
  Unfocus.
  Focus 7.
  apply Qle_trans with
    ((c # 1) + (d # 1) + 1 + 1).
  clear - H0.
  psatz Q.
  auto.
  Unfocus.
  Focus 6.
  apply Qle_trans with
    ((1 + ((c # 1) + (d # 1) + 1)) / ratio).
  clear - le H16.
  apply Qle_shift_div_l.
  psatz Q.
  psatz Q.
  apply Qle_trans with
    ((1 + ((c # 1) + (d # 1) + 1)) / ((delta + 1) / delta)).
  apply Qmult_le_compat_l.
  clear - H4 H16 H11.
  apply Qle_shift_inv_l.
  apply Qlt_shift_div_l.
  psatz Q.
  psatz Q.
  rewrite Qmult_comm.
  apply Qle_shift_div_r.
  psatzl Q.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4.
  psatz Q.
  field_simplify.
  apply Qle_trans with
    (   (delta * (d # 1) + delta + (-1 # 1) * (c # 1) +
    (-1 # 1)) * delta).
  apply Qmult_le_0_compat.
  clear - H19.
  psatz Q.
  clear - H4.
  psatz Q.
  field_simplify.
  intuition.
  clear - H10 H4.
  split.
  psatz Q.
  psatz Q.
  Unfocus.
  Focus 6.
  apply Qle_trans with ((b # 1) + 1).
  rewrite <- H2.
  clear - H0.
  psatz Q.
  clear - H12 H0 H4.
  psatz Q.
  Unfocus.
  Focus 2.
  assert (delta * ((a # 1) + 1) < (b # 1) + 1).
  case_eq (Qlt_le_dec (delta * ((a # 1) + 1)) ((b # 1) + 1)).
  intro q.
  intro cl.
  clear cl.
  auto.
  intro q.
  intro cl.
  clear cl.
  apply False_ind.
  apply H23.
  auto.
  clear - H18.
  psatz Q.
  apply Qle_trans with
    (((b # 1) + 1) / delta).
  clear - H1 H4.
  apply Qle_shift_div_l.
  psatz Q.
  psatz Q.
  apply Qle_shift_div_r.
  clear - H4.
  psatz Q.
  rewrite <- H2.
  apply Qle_trans with
    ((c # 1) + (d # 1) + 1 + 1 + delta * ((c # 1) + (d # 1) + 1 + 1)).
  clear - H14.
  psatz Q.
  assert (0 <= ((c # 1) + (d # 1) + 1 + 1)).
  clear - H0 H8.
  psatz Q.
  generalize H25.
  clear H25.
  generalize ((c # 1) + (d # 1) + 1 + 1).
  intro q.
  intro qnonneg.
  clear - qnonneg H10 H4.
  psatz Q.
  Unfocus.
  Focus 3.
  case (Qlt_le_dec (a # 1) 1).
  intro small.
  assert (a = 0%Z).
  generalize H.
  generalize small.
  clear.
  compute -[Zle Zmult Zplus Zlt].
  intro small.
  intro large.
  intuition.
  clear H.
  clear small.
  rewrite H1 in H7.
  rewrite H1 in H12.
  rewrite H1 in H23.
  rewrite H1 in H18.
  rewrite H1.
  clear H1.
  clear H7.
  ring_simplify.
  assert ((b # 1) <= (7 # 1)).
  clear H23.
  clear H24.
  clear H22.
  clear H21.
  clear H17.
  assert ((b # 1) + 1 < (9 # 2) * (1 + 0 + 1)).
  apply Qle_lt_trans with (delta * (1 + 0 + 1)).
  auto.
  apply Qmult_lt_compat_r.
  intuition.
  auto.
  generalize H.
  clear.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  (* case analysis b == 7 or not *)
  case (Qlt_le_dec (b # 1) (7 # 1)).
  Focus 2.
  intro large.
  assert ((b # 1) == (7 # 1)).
  clear - H large.
  apply Qle_antisym.
  auto.
  auto.
  rewrite H1 in *.
  clear large.
  clear H.
  clear H6.
  clear H18.
  apply Qle_trans with (4 # 1).
  assert ((c # 1) + (d # 1) <= (4 # 1)).
  case (Qlt_le_dec (4 # 1) ((c # 1) + (d # 1))).
  intro large.
  apply False_ind.
  assert (5 # 1 <= (c # 1) + (d # 1)).
  clear - large.
  generalize large.
  clear large.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear large.
  assert ( (7 # 1) /delta <= (e # 1) + 1).
  apply Qle_shift_div_r.
  clear - H4.
  psatz Q.
  apply Qle_trans with ((c # 1) + (d # 1) + 1 + 1).
  clear - H.
  psatz Q.
  clear - H20.
  psatz Q.
  assert ((e # 1) > 0).
  case (Qlt_le_dec 0 (e # 1)).
  tauto.
  intro ezero.
  apply False_ind.
  assert ((e # 1) == 0).
  apply Qle_antisym.
  auto.
  auto.
  clear ezero.
  rewrite H7 in *.
  assert ((7 # 1) <= delta).
  clear - H6 H4.
  apply Qle_trans with
    (((7 # 1) / delta) * delta).
  clear H6.
  field_simplify.
  intuition.
  psatz Q.
  apply Qle_trans with ((0 + 1) * delta).
  apply Qmult_le_compat_r.
  auto.
  clear H6.
  psatz Q.
  psatzl Q.
  clear - H15 H18.
  psatz Q.
  clear H6.
  assert (1 <= (e # 1)).
  clear - H7.
  generalize H7.
  clear H7.
  compute -[Zle Zmult Zplus Zlt].
  psatz Z.
  clear H7.
  clear H1.
  clear - H H2 H6.
  psatz Q.
  auto.
  case (Qlt_le_dec 0 (d # 1)).
  intro large.
  assert (1 <= (d # 1)).
  clear - large.
  generalize large.
  clear large.
  compute -[Zle Zmult Zplus Zlt].
  psatz Z.
  clear large.
  clear - H H6.
  psatz Q.
  intro small.
  assert ((d # 1) == 0).
  apply Qle_antisym.
  exact small.
  assumption.
  clear small.
  rewrite H6 in *.
  case (Qlt_le_dec (4 # 1) ((c # 1) + 1)).
  intro lt.
  apply False_ind.
  assert ((c # 1) == (4 # 1)).
  clear - H lt.
  generalize H lt.
  clear H lt.
  compute -[Zle Zmult Zplus Zlt].
  psatz Z.
  rewrite H7 in *.
  clear lt H.
  clear - H19 H15.
  psatz Q.
  auto.
  clear - H12.
  psatz Q.
  Unfocus.
  Focus 3.
  clear H.
  intro b7.
  case (Qlt_le_dec (b # 1) (5 # 1)).
  intro b5.
  clear b7.
  case (Qlt_le_dec (b # 1) (3 # 1)).
  intro b3.
  clear b5.
  clear H17 H21 H22 H24 H23.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + 1) * delta / (delta + 1)).
  clear - H19 H4.
  apply Qle_shift_div_l.
  psatz Q.
  psatz Q.
  apply Qle_trans with
    ((((b # 1) + 1) * delta / (delta + 1)) * delta / (delta + 1)).
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  clear - H2 H14 H20 H4 H3 H9.
  apply Qle_shift_div_l.
  clear - H4.
  psatz Q.
  rewrite <- H2.
  clear H2.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + 1 + (e # 1) + 1) * delta).
  assert (0 <= (c # 1) + (d # 1) + 1 + 1).
  clear - H3.
  psatz Q.
  generalize dependent ((c # 1) + (d # 1) + 1 + 1).
  clear H3.
  intro x.
  psatz Q.
  ring_simplify.
  intuition.
  psatz Q.
  apply Qle_shift_inv_l.
  psatz Q.
  intuition.
  apply Qle_trans with
    ((4 # 1) * delta / (delta + 1) * delta / (delta + 1)).
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  clear - b3.
  psatz Q.
  clear - H4.
  psatz Q.
  apply Qle_shift_inv_l.
  clear - H4; psatz Q.
  intuition.
  clear - H4; psatz Q.
  apply Qle_shift_inv_l.
  clear - H4; psatz Q.
  intuition.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4.
  psatz Q.
  field_simplify.
  clear - H4.
  apply Qle_trans with
    ((delta ^ 2 + (-2 # 1) * delta + 1) * delta).
  apply Qmult_le_0_compat.
  psatz Q.
  psatz Q.
  field_simplify.
  intuition.
  psatz Q.
  Focus.
  intro b3.
  assert (b # 1 <= 4 # 1).
  clear - b5.
  generalize b5.
  clear b5.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear b5.
  rename H into b4.
  assert (((c # 1) + (d # 1) + 1 + 1) <= (4 # 1)).
  clear - H2 b4 H9.
  rewrite <- H2 in b4.
  clear H2.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  psatz Q.
  case (Qlt_le_dec (c # 1) (2 # 1)).
  intro csmall.
  apply Qle_trans with (1 + 1).
  assert (c # 1 <= 1).
  clear - csmall.
  generalize csmall.
  clear csmall.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  apply Qplus_le_compat.
  auto.
  intuition.
  clear - H4 H10.
  psatz Q.
  intro I.
  assert ((c # 1) == (2 # 1)).
  apply Qle_antisym.
  clear - H H8.
  psatz Q.
  assumption.
  rewrite H1 in *.
  ring_simplify.
  clear I.
  assert (d # 1 == 0).
  clear - H8 H.
  psatz Q.
  rewrite H7 in *.
  clear H.
  clear H17 H21 H22 H24 H23.
  case (Qlt_le_dec (e # 1) 1).
  intro esmall.
  assert ((e # 1) == 0).
  clear - esmall H9.
  generalize esmall H9.
  clear esmall H9.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear esmall.
  rewrite H in *.
  clear - H20.
  psatz Q.
  intro elarge.
  clear - H2 b4 H1 H7 elarge.
  apply False_ind.
  rewrite <- H2 in b4.
  clear H2.
  psatz Q.
  Unfocus.
  Focus 3.
  intro b5.
  assert ((c # 1) + (d # 1) + 1 + 1 <= 5 # 1).
  assert (b # 1 <= (6 # 1)).
  clear - b7.
  generalize b7.
  clear b7.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear - H2 H6 H8 H9 H14 H20 H H4 H10 H15.
  case (Qlt_le_dec (e # 1) 1).
  intro esmall.
  assert (e # 1 == 0).
  clear - esmall H9.
  generalize esmall H9.
  clear esmall H9.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  rewrite H0 in *.
  clear esmall.
  rewrite <- H2 in *.
  clear H2.
  clear - H20 H15.
  assert ((c # 1) + (d # 1) + 1 + 1 < 9 # 2).
  apply Qle_lt_trans with (delta * ( 0 + 1)).
  auto.
  clear - H15.
  psatz Q.
  clear - H.
  psatz Q.
  intro elarge.
  clear - elarge H2 H.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro eq.
  rewrite <- eq in H.
  clear eq.
  psatz Q.
  case (Qlt_le_dec 0 (d # 1)).
  Focus 2.
  intro dsmall.
  assert (d # 1 == 0).
  apply Qle_antisym.
  assumption.
  assumption.
  rewrite H1 in *.
  clear - H19.
  ring_simplify in H19.
  assumption.
  Unfocus.
  Focus 3.
  intro dlarge.
  assert (1 <= d # 1).
  clear - dlarge.
  generalize dlarge; clear dlarge; compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear dlarge.
  apply Qle_trans with (3 # 1).
  clear - H H1.
  psatz Q.
  clear - H12 b5.
  psatz Q.
  Unfocus.
  Focus 3.
  intro alarge.
  case (Qlt_le_dec (a # 1) (2 # 1)).
  intro asmall.
  assert (a#1 == 1) as aone.
  clear - alarge asmall.
  generalize alarge asmall; clear alarge asmall.
  compute -[Zmult Zle Zplus Zlt].
  psatz Z.
  clear alarge asmall.
  rewrite aone in *.
  clear aone.
  case (Qlt_le_dec (111 # 25) delta).
  Focus 2.
  intro deltasmall.
  clear H15.
  clear H17 H21 H22 H24 H23.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + 1) * delta / (delta + 1)).
  clear - H19 H4.
  apply Qle_shift_div_l.
  clear - H4.
  psatz Q.
  psatz Q.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + (e # 1) + 1 + 1) * (delta / (delta + 1)) * (delta / (delta + 1))).
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4.
  psatz Q.
  field_simplify.
  clear - H4 H20 H10.
  apply Qle_trans with
    (delta * (delta * (e # 1) + delta + (-1 # 1) * (c # 1) +
    (-1 # 1) * (d # 1) + (-2 # 1)) / 1).
  apply Qmult_le_0_compat.
  apply Qmult_le_0_compat.
  clear - H4.
  psatz Q.
  psatz Q.
  apply Qle_shift_inv_l.
  intuition.
  intuition.
  field_simplify.
  intuition.
  clear - H4.
  psatz Q.
  rewrite H2.
  apply Qle_trans with
    ((delta * (1 + 1 + 1)) * (delta / (delta + 1)) * (delta / (delta + 1))).
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  assumption.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  ring_simplify.
  clear - H4; psatz Q.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  clear -H4; psatz Q.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  field_simplify.
  clear - H4 H10 deltasmall.
  apply Qle_trans with
    (delta * ((-1 # 1) * delta ^ 2 + (4 # 1) * delta + (2 # 1))).
  apply Qmult_le_0_compat.
  clear - H4; psatz Q.
  clear H10.
  psatz Q.
  field_simplify.
  intuition.
  psatz Q.
  Unfocus.
  Focus 3.
  intro deltalarge.
  clear H4 H10.
  apply Qle_trans with (8 # 1).
  assert (((c # 1) + (d # 1) + 1 + 1) <= (10 # 1)).
  assert (((c # 1) + (d # 1) + 1 + (e # 1) + 1 + 1) <= (13 # 1)).
  rewrite H2.
  clear - H12 H15.
  assert (((b # 1) + 1) < (9# 2) * (1 + 1 + 1)).
  apply Qle_lt_trans with (delta * (1 + 1 + 1)).
  assumption.
  psatz Q.
  clear - H.
  ring_simplify in H.
  generalize H; clear H.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear - H15 H1 H20 H9.
  assert (((c # 1) + (d # 1) + 1 + 1 + (e # 1) + 1) <= (13 # 1)).
  clear -H1; psatz Q.
  clear H1.
  assert (((c # 1) + (d # 1) + 1 + 1) < (11 # 1)).
  generalize dependent ((c # 1) + (d # 1) + 1 + 1).
  intro x.
  intro xsmall.
  assert (x <= (9 # 2) * ((e # 1) + 1)).
  apply Qle_trans with (delta * ((e # 1) + 1)).
  exact xsmall.
  clear xsmall.
  apply Qmult_le_compat_r.
  clear - H15; psatz Q.
  clear - H9 ; psatz Q.
  clear H15 xsmall.
  psatz Q.
  clear - H0.
  generalize H0; clear H0; compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear - H0 H8 H1 H19 H15.
  assert ((c # 1) + 1 < (9 # 1)).
  assert ((c # 1) + 1 <= (9 # 2) * ((d # 1) + 1)).
  apply Qle_trans with (delta * ((d # 1) + 1)).
  assumption.
  clear - H8 H15.
  psatz Q.
  clear - H1 H.
  psatz Q.
  clear - H; generalize H; clear H; compute -[Zmult Zplus Zle Zlt]; psatz Z.
  clear - deltalarge.
  psatz Q.
  Unfocus.
  Focus 3.
  clear alarge; intro alarge.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + 1) * (delta / (delta + 1))).
  clear - H4 H8 H0 H19.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  field_simplify.
  clear - H19.
  generalize dependent (c # 1).
  generalize dependent (d # 1).
  intros x y.
  intro z.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  psatz Q.
  clear - H4.
  psatz Q.
  apply Qle_trans with
    (((b # 1) + 1) * (delta / (delta + 1)) * (delta / (delta + 1))).
  apply Qmult_le_compat_r.
  rewrite <- H2.
  clear - H20 H3 H9 H4.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intros.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  clear - H20; psatz Q.
  clear - H4; psatz Q.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  ring_simplify.
  clear - H4; psatz Q.
  apply Qle_trans with
    (delta * ((1 + (a # 1) + 1)) * (delta / (delta + 1)) * (delta / (delta + 1))).
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  assumption.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  ring_simplify.
  clear - H4; psatz Q.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  ring_simplify; clear - H4; psatz Q.
  rewrite <- Qmult_assoc.
  rewrite <- Qmult_assoc.
  apply Qmult_le_compat_l.
  clear - alarge H15 H4.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4.
  psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  clear; intuition.
  apply Qle_trans with 0.
  clear; intuition.
  apply Qle_trans with
    ((-1 # 1) * delta ^ 2 + (2 # 1) * delta * (2 # 1) + (2 # 1) * delta +
      (2 # 1) + 1).
  clear alarge.
  psatz Q.
  eapply Qle_minus_iff; ring_simplify.
  clear H15; psatz Q.
  clear - H4; psatz Q.
  clear - H4; psatz Q.
  Unfocus.
  case (Qlt_le_dec delta (5 # 2)).
  intro delta52.
  clear H17 H21 H22 H24.
  clear H15.
  case (Qlt_le_dec (2 # 1) (a # 1)).
  intro alarge.
  assert ((3 # 1) <= (a # 1)) as a3.
  clear - alarge.
  generalize alarge; clear alarge.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear alarge.
  apply Qle_trans with
    (((b # 1) + 1) * (delta / (delta + 1))).
  rewrite <- H2.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear -H4; psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  clear; intuition.
  apply Qle_trans with 0.
  clear; intuition.
  clear - H20.
  psatz Q.
  clear - H4; psatz Q.
  apply Qle_trans with
    (delta * (1 + (a # 1) + 1) * (delta / (delta + 1))).
  apply Qmult_le_compat_r.
  auto.
  apply Qle_shift_div_l.
  clear - H4; psatz Q.
  ring_simplify.
  clear - H4; psatz Q.
  apply Qle_trans with
    (delta * ((1 + (a # 1) + 1) * (delta / (delta + 1)))).
  ring_simplify.
  intuition.
  apply Qmult_le_compat_l.
  assert ((delta / (delta + 1)) <= (5 # 7)).
  clear - H4 delta52 H10.
  apply Qle_shift_div_r.
  clear - H4; psatz Q.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear; intuition.
  apply Qle_trans with 0.
  clear; intuition.
  clear - delta52.
  psatz Q.
  apply Qle_trans with
    ((1 + (a # 1) + 1) * (5 # 7)).
  apply Qmult_le_compat_l.
  assumption.
  clear - a3; psatz Q.
  clear - a3; psatz Q.
  clear - H4; psatz Q.
  intro a2.
  clear H7.
  case (Qlt_le_dec 1 (a # 1)).
  intro a1.
  assert ((a # 1) == (2 # 1)) as atwo.
  clear - a2 a1; generalize a1 a2; clear a1 a2; compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear a1 a2.
  rewrite atwo in *.
  clear atwo.
  clear H.
  assert ((b # 1) + 1 <= (9 # 1)) as bnine.
  assert ((b # 1) + 1 < (10 # 1)).
  apply Qle_lt_trans with (delta * (1 + (2 # 1) + 1)).
  auto.
  clear - delta52.
  psatz Q.
  clear - H.
  generalize H; clear H.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  assert ((c # 1) + (d # 1) + 1 + 1 <= (6 # 1)).
  assert ((c # 1) + (d # 1) + 1 + 1 < (7 # 1)).
  rewrite <- H2 in bnine.
  clear - bnine delta52 H4 H9 H20.
  assert ((c # 1) + (d # 1) + 1 + 1 < (5 # 2) * ((e # 1) + 1)).
  apply Qle_lt_trans with (delta * ((e # 1) + 1)).
  auto.
  apply Qmult_lt_compat_r.
  clear - H9; psatz Q.
  auto.
  clear H20 delta52.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  psatz Q.
  clear - H.
  generalize H; clear H; compute -[Zmult Zle Zlt Zplus].
  psatz Z.
  apply Qle_trans with (6 # 1).
  assumption.
  clear - H4 H10.
  psatz Q.
  intro aone.
  case (Qlt_le_dec (a # 1) 1).
  clear aone.
  intro aone.
  clear a2.
  assert ((a # 1) == 0).
  clear - aone H.
  generalize H aone; clear H aone; compute -[Zmult Zle Zlt Zplus].
  psatz Z.
  rewrite H1 in *.
  clear aone.
  clear H.
  clear H1.
  assert ((b # 1) + 1 <= (4 # 1)).
  assert ((b # 1) + 1 < ( 5 # 1)).
  apply Qle_lt_trans with (delta * (1 + 0 + 1)).
  assumption.
  clear - delta52; psatz Q.
  clear - H; generalize H; clear H; compute -[Zmult Zle Zlt Zplus]; psatz Z.
  assert (((c # 1) + (d # 1) + 1 + 1) <= (2 # 1)).
  assert (((c # 1) + (d # 1) + 1 + 1) <  ( 3 # 1)).
  rewrite <- H2 in H.
  clear - delta52 H20 H9 H4 H.
  assert ((c # 1) + (d # 1) + 1 + 1 < (5 # 2) * ((e # 1) + 1)).
  apply Qle_lt_trans with (delta * ((e # 1) + 1)).
  assumption.
  apply Qmult_lt_compat_r.
  clear - H9; psatz Q.
  assumption.
  clear H20 delta52.
  generalize dependent ((c # 1) + (d # 1)).
  intro x.
  psatz Q.
  clear - H1; generalize H1; clear H1; compute -[Zmult Zle Zlt Zplus]; psatz Z.
  apply Qle_trans with (2 # 1).
  assumption.
  clear - H4 H10.
  psatz Q.
  clear a2.
  intro abelone.
  assert ((a # 1) == 1) as a1.
  apply Qle_antisym.
  assumption.
  assumption.
  rewrite a1 in *.
  clear aone.
  clear abelone.
  clear H.
  assert ((b # 1) + 1 <= (7 # 1)) as bsmall.
  assert ((b # 1) + 1 <  (8 # 1)).
  clear - H12 delta52.
  psatz Q.
  clear - H; generalize H; clear H; compute -[Zplus Zmult Zle Zlt].
  psatz Z.
  assert ((c # 1) + (d # 1) + 1 + 1 <= (4 # 1)).
  assert ((c # 1) + (d # 1) + 1 + 1 <  (5 # 1)).
  rewrite <- H2 in bsmall.
  assert (ratio < (3 # 2)) as ratiosmall.
  clear - H5 delta52.
  psatz Q.
  clear H5.
  clear H2.
  assert (1 + ((c # 1) + (d # 1) + 1) < (3 # 2) * (1 + (e # 1))) as lt_sp.
  apply Qlt_trans with (ratio * (1 + (e # 1))).
  assumption.
  apply Qmult_lt_compat_r.
  clear - H9; psatz Q.
  assumption.
  clear - lt_sp bsmall.
  psatz Q.
  clear - H.
  generalize H; clear H; compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  apply Qle_trans with (4 # 1).
  assumption.
  clear - H4 H10.
  psatz Q.
  intro delta52.
  case (Qlt_le_dec delta (3 # 1)).
  intro delta3.
  clear H21 H22 H24.
  assert (ratio <= 3 # 2) as ratio32.
  apply H17.
  assumption.
  assumption.
  clear H17.
  (* the only needed special case is a == 0 *)
  case (Qlt_le_dec (a # 1) 1).
  intro a1.
  assert ((a # 1) == 0) as a0.
  clear - a1 H.
  generalize a1 H; compute -[Zmult Zle Zplus Zlt]; psatz Z.
  rewrite a0 in *.
  clear a1.
  clear H7.
  clear H.
  assert (((b # 1) + 1) <= (5 # 1)) as bone5.
  assert (((b # 1) + 1) < (6 # 1)) as bone6.
  clear - H12 delta3.
  psatz Q.
  clear - bone6.
  generalize bone6; compute -[Zmult Zle Zplus Zlt].
  psatz Z.
  assert (1 + ((c # 1) + (d # 1) + 1) < (3 # 1)) as cd11small.
  rewrite <- H2 in bone5.
  clear a0.
  clear - bone5 ratio32 lt H9.
  assert (1 + ((c # 1) + (d # 1) + 1) < (3 # 2) * (1 + (e # 1))) as lt_spec.
  apply Qlt_le_trans with (ratio * (1 + (e # 1))).
  assumption.
  apply Qmult_le_compat_r.
  assumption.
  clear - H9; psatz Q.
  clear ratio32 lt.
  psatz Q.
  assert (1 + ((c # 1) + (d # 1) + 1) <= 2 # 1) as cd2.
  clear - cd11small.
  generalize cd11small.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  apply Qle_trans with (2 # 1).
  clear cd11small.
  clear - cd2; psatz Q.
  clear - H4 H10; psatz Q.
  intro a1.
  apply Qle_trans with
    (((b # 1) + 1) * (ratio / (ratio + 1))).
  rewrite <- H2.
  assert (ratio > 0) as rpos.
  apply Qlt_le_trans with ((delta + 1) / delta).
  apply Qlt_shift_div_l.
  clear - H4; psatz Q.
  ring_simplify.
  clear - H4; psatz Q.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  clear - lt H9 rpos.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro one.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - rpos; psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  clear; intuition.
  apply Qle_trans with 0.
  clear; intuition.
  clear - one; psatz Q.
  clear - rpos; psatz Q.
  apply Qle_trans with
    (((delta * (1 + (a # 1) + 1))) * (ratio / (ratio + 1))).
  apply Qmult_le_compat_r.
  auto.
  apply Qle_shift_div_l.
  clear - H16; psatz Q.
  ring_simplify.
  clear - H16; psatz Q.
  apply Qle_trans with
    (delta * ((1 + (a # 1) + 1) * (ratio / (ratio + 1)))).
  ring_simplify.
  intuition.
  apply Qmult_le_compat_l.
  assert ((ratio / (ratio + 1)) <= 2 # 3).
  apply Qle_shift_div_r.
  clear - H16; psatz Q.
  clear - ratio32 H16.
  psatz Q.
  apply Qle_trans with
    ((1 + (a # 1) + 1) * (2 # 3)).
  apply Qmult_le_compat_l.
  assumption.
  clear - H; psatz Q.
  clear - a1.
  psatz Q.
  clear - H4; psatz Q.
  clear delta52.
  intro delta3.
  clear H17.
  case (Qlt_le_dec delta (7 # 2)).
  intro delta72.
  clear H22 H24.
  assert (ratio <= (2 # 1)) as ratio2.
  apply H21.
  assumption.
  assumption.
  clear H21.
  case (Qlt_le_dec (a # 1) 1).
  intro asmall.
  assert ((a # 1) == 0) as a0.
  clear - asmall H.
  generalize H asmall.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  rewrite a0 in *.
  clear asmall H.
  clear a0.
  assert (((b # 1) + 1) <= 6 # 1) as bone6.
  assert (((b # 1) + 1) <  7 # 1) as bone7.
  clear - H12 delta72.
  psatz Q.
  clear - bone7.
  generalize bone7.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  apply Qle_trans with (3 # 1).
  assert ((c # 1) + (d # 1) + 1 + 1 < (4 # 1)) as cd4.
  rewrite <- H2 in bone6.
  clear - bone6 lt ratio2 H3 H9.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  psatz Q.
  clear - cd4.
  generalize cd4.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear - delta3.
  psatz Q.
  intro aone.
  apply Qle_trans with
    (((b # 1) + 1) * ratio / (ratio + 1)).
  rewrite <- H2.
  clear - lt H3 H9 H16.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro one.
  intro xnneg.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H16; psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  clear - one; psatz Q.
  psatz Q.
  apply Qle_trans with
    ((delta * (1 + (a # 1) + 1)) * ratio / (ratio + 1)).
  apply Qmult_le_compat_r.
  apply Qmult_le_compat_r.
  auto.
  clear - H16; psatz Q.
  apply Qle_shift_inv_l.
  clear - H16; psatz Q.
  intuition.
  apply Qle_trans with
    (delta * ((1 + (a # 1) + 1) * ratio / (ratio + 1))).
  field_simplify.
  intuition.
  psatz Q.
  psatz Q.
  apply Qmult_le_compat_l.
  assert (ratio / (ratio + 1) <= (2 # 3)) as ratio23.
  clear - ratio2 H16.
  apply Qle_shift_div_r.
  psatz Q.
  psatz Q.
  apply Qle_trans with ((1 + (a # 1) + 1) * (2 # 3)).
  apply Qle_trans with ((1 + (a # 1) + 1) * (ratio / (ratio + 1))).
  field_simplify.
  intuition.
  psatz Q.
  psatz Q.
  apply Qmult_le_compat_l.
  assumption.
  clear - H7; psatz Q.
  clear - aone.
  psatz Q.
  clear - H4; psatz Q.
  intro delta72.
  clear delta3.
  clear H21.
  case (Qlt_le_dec delta (4 # 1)).
  intro delta4.
  clear H24.
  assert (ratio <= 4 # 3) as r43.
  apply H22.
  assumption.
  assumption.
  clear H22.
  case (Qlt_le_dec (a # 1) 1).
  intro asmall.
  assert ((a # 1) == 0) as a0.
  clear - asmall H.
  generalize H asmall.
  compute -[Zmult Zplus Zlt Zle].
  psatz Z.
  rewrite a0 in *.
  clear asmall H.
  clear H7.
  clear a0.
  assert (((b # 1) + 1) <= (7 # 1)) as b7.
  assert (((b # 1) + 1) < (8 # 1)) as b8.
  clear - H12 delta4.
  psatz Q.
  clear - b8.
  generalize b8; compute -[Zmult Zplus Zle Zlt]; psatz Z.
  assert (((c # 1) + (d # 1) + 1 + 1) < (4 # 1)).
  apply Qlt_le_trans with
    (((b # 1) + 1) * (ratio / (ratio + 1))).
  rewrite <- H2.
  clear - H3 H16 lt H9.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro r.
  intro xpos.
  eapply Qlt_minus_iff.
  field_simplify.
  apply Qlt_shift_div_l.
  psatz Q.
  field_simplify.
  apply Qlt_shift_div_l.
  intuition.
  apply Qle_lt_trans with 0.
  intuition.
  psatz Q.
  psatz Q.
  clear -r43 b7 H16.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  psatz Q.
  psatz Q.
  apply Qle_trans with (3 # 1).
  clear - H.
  generalize H.
  compute -[Zmult Zplus Zle Zlt].
  psatz Z.
  clear - delta72.
  psatz Q.
  intro aone.
  apply Qle_trans with
    (((b # 1) + 1) * (ratio / (ratio + 1))).
  rewrite <- H2.
  clear - lt H3 H9 H16.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro r.
  intro xp.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H16; psatz Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  clear - r; psatz Q.
  psatz Q.
  assert ((ratio / (ratio + 1)) <= 4 # 7).
  clear -r43 H16.
  apply Qle_shift_div_r.
  clear - H16; psatz Q.
  psatz Q.
  apply Qle_trans with
    (((b # 1) + 1) * (4 # 7)).
  apply Qmult_le_compat_l.
  assumption.
  clear - H6; psatzl Q.
  apply Qle_trans with
    ((delta * (1 + (a # 1) + 1)) * (4 # 7)).
  apply Qmult_le_compat_r.
  auto.
  intuition.
  rewrite <- Qmult_assoc.
  apply Qmult_le_compat_l.
  clear - aone.
  psatzl Q.
  clear - H4; psatzl Q.
  intro delta4.
  clear delta72.
  clear H22.
  assert (ratio <= 5 # 3) as r53.
  apply H24.
  assumption.
  assumption.
  case (Qlt_le_dec (a # 1) 1).
  intro asmall.
  assert ((a # 1) == 0) as a0.
  clear - asmall H.
  generalize H asmall; compute -[Zmult Zplus Zle Zlt]; psatzl Z.
  rewrite a0 in *.
  clear a0.
  clear asmall H7 H.
  assert ((b # 1) + 1 <= (8 # 1)) as b8.
  assert ((b # 1) + 1 <  (9 # 1)) as b9.
  clear - H12 H15.
  psatzl Q.
  clear -b9.
  generalize b9.
  compute -[Zmult Zplus Zle Zlt].
  psatzl Z.
  assert ((c # 1) + (d # 1) + 1 + 1 < (5 # 1)).
  apply Qlt_le_trans with
    (((b # 1) + 1) * (ratio / (ratio + 1))).
  rewrite <- H2.
  clear - lt H3 H9 H16.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro xr.
  intro xnneg.
  eapply Qlt_minus_iff.
  field_simplify.
  apply Qlt_shift_div_l.
  psatzl Q.
  field_simplify.
  apply Qlt_shift_div_l.
  intuition.
  apply Qle_lt_trans with 0.
  intuition.
  psatzl Q.
  psatzl Q.
  clear - b8 r53 H16.
  apply Qle_trans with
    ((8 # 1) * (ratio / (ratio + 1))).
  apply Qmult_le_compat_r.
  assumption.
  apply Qle_shift_div_l.
  psatzl Q.
  ring_simplify.
  psatzl Q.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  clear b8.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with (4 # 1).
  clear - H.
  generalize H.
  compute -[Zmult Zplus Zle Zlt].
  psatzl Z.
  clear - delta4.
  psatzl Q.
  intro aone.
  apply Qle_trans with
    (((b # 1) + 1) * (ratio / (ratio + 1))).
  rewrite <- H2.
  clear - H3 H9 lt H16.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  clear c d.
  intro one.
  intro two.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with
    ((delta * (1 + (a # 1) + 1)) * (ratio / (ratio + 1))).
  apply Qmult_le_compat_r.
  auto.
  apply Qle_shift_div_l.
  psatzl Q.
  ring_simplify.
  psatzl Q.
  apply Qle_trans with
    (delta * ((1 + (a # 1) + 1) * (ratio / (ratio + 1)))).
  ring_simplify.
  intuition.
  apply Qmult_le_compat_l.
  apply Qle_trans with
    ((1 + (a # 1) + 1) * (5 # 8)).
  apply Qmult_le_compat_l.
  clear - r53 H16.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with
    (((a # 1) + 1) + ((c # 1) + (d # 1) + 1 + 1)).
  ring_simplify.
  intuition.
  apply Qle_trans with
    ((((b # 1) + 1) / delta) + ratio * (1 + (e # 1))).
  apply Qplus_le_compat.
  apply Qle_shift_div_l.
  psatzl Q.
  case (Qlt_le_dec ((b # 1) + 1) (((a # 1) + 1) * delta)).
  intro bsmall.
  apply False_ind.
  apply H23.
  clear - bsmall; psatzl Q.
  clear - H18; psatzl Q.
  auto.
  clear -lt; psatzl Q.
  apply Qle_trans with
    ((((e # 1) + 1) * ((ratio + 1) / delta)) +
      ((delta - 1) * ((e # 1) + 1))).
  apply Qplus_le_compat.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  rewrite <- H2.
  clear - lt H16.
  psatzl Q.
  psatzl Q.
  clear - H9 H5 H16.
  psatz Q.
  apply Qle_trans with
    (((e # 1) + 1) * (((ratio + 1) / delta) + (delta - 1))).
  ring_simplify.
  intuition.
  apply Qle_trans with
    (((e # 1) + 1) * delta).
  apply Qmult_le_compat_l.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  field_simplify.
  apply Qle_shift_div_l.
  intuition.
  apply Qle_trans with 0.
  intuition.
  clear - H5.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  clear H17 H21 H22 H24.
  (* we should use the smallness of a *)
  assert (((a # 1) + 1 < (((b # 1) + 1) / delta))) as asmall.
  apply Qlt_shift_div_l.
  psatzl Q.
  case (Qlt_le_dec (((a # 1) + 1) * delta) ((b # 1) + 1)).
  auto.
  intro blea.
  apply False_ind.
  apply H23.
  clear - blea; psatzl Q.
  psatzl Q.
  assert (((b # 1) + 1) <= ((c # 1) + 1) * (1 + delta) * ((ratio + 1) / ratio)) as bsmall.
  apply Qle_trans with
    (((c # 1) + (d # 1) + 1 + 1) * ((ratio + 1) / ratio)).
  clear - le H2 H3 H9 H16.
  rewrite <- H2.
  clear H2.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  intro one.
  intro two.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  apply Qle_trans with 0.
  intuition.
  psatzl Q.
  psatzl Q.
  apply Qmult_le_compat_r.
  clear - H4 H13.
  psatzl Q.
  apply Qle_shift_div_l.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with
    (((c # 1) + 1) * ((1 + delta) / delta) * ((ratio + 1) / ratio)).
  apply
    Qle_trans with (((b # 1) + 1) / delta).
  psatzl Q.
  clear - bsmall H4 H16.
  apply Qle_shift_div_r.
  psatzl Q.
  apply Qle_trans with
    (((c # 1) + 1) * (1 + delta) * ((ratio + 1) / ratio)).
  assumption.
  field_simplify.
  intuition.
  split.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with
    (((c # 1) + 1) * delta).
  apply Qle_trans with
    (((c # 1) + 1) * (((1 + delta) / delta) * ((ratio + 1) / ratio))).
  field_simplify.
  intuition.
  psatzl Q.
  psatzl Q.
  apply Qmult_le_compat_l.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  clear - H4 H10 H16.
  psatz Q.
  apply Qle_trans with 0.
  intuition.
  apply Qle_trans with
    (ratio * (delta ^ 2 + (-1 # 1) * delta + (-1 # 1)) + ((-1 # 1) * delta + (-1 # 1))).
  apply Qle_trans with
    (((delta + 1) / delta) * (delta ^ 2 + (-1 # 1) * delta + (-1 # 1)) +
    ((-1 # 1) * delta + (-1 # 1))).
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  apply Qle_trans with 0.
  intuition.
  clear - H4 H10.
  psatz Q.
  psatzl Q.
  apply Qplus_le_compat.
  apply Qmult_le_compat_r.
  apply Qle_shift_div_r.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  intuition.
  ring_simplify.
  intuition.
  psatzl Q.
  psatzl Q.
  psatzl Q.
  (* this is an important point *)
  apply Qle_trans with
    (((a # 1) + 1) + ((c # 1) + 1)).
  psatzl Q.
  apply Qle_trans with
    (delta * ((e # 1) + 1) + delta * ((d # 1) + 1 )).
  apply Qplus_le_compat.
  apply Qle_trans with (((b # 1) + 1) / delta).
  case (Qlt_le_dec (((a # 1) + 1) * delta) (((b # 1) + 1))).
  intro lt.
  apply Qlt_le_weak.
  apply Qlt_shift_div_l.
  psatzl Q.
  assumption.
  intro f.
  apply False_ind.
  apply H23.
  clear -f H4.
  psatzl Q.
  psatzl Q.
  apply Qle_trans with
    (delta * ((b # 1) + 1)/ (delta + 1)).
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  apply Qle_trans with 0.
  intuition.
  apply Qle_trans with
    (((b # 1) + 1) * (delta ^2 - delta - 1)).
  apply Qmult_le_0_compat.
  psatzl Q.
  clear - H4 H10.
  psatz Q.
  ring_simplify.
  intuition.
  psatzl Q.
  apply Qle_trans with
    (delta * (((b # 1) + 1) / (delta + 1))).
  field_simplify.
  intuition.
  psatzl Q.
  psatzl Q.
  apply Qmult_le_compat_l.
  apply Qle_shift_div_r.
  psatzl Q.
  rewrite <- H2.
  clear - H3 H4 H20.
  generalize dependent ((c # 1) + (d # 1) + 1).
  intro x.
  psatz Q.
  psatzl Q.
  auto.
  ring_simplify.
  intuition.
  Qed.


Lemma NR_shallow_insert:
  good_params -> forall (a e: Z),
  shallow_insert isBalancedSize isSingleSize (a#1) (e#1).
  unfold good_params.
  unfold normal, slope, curve, deltasup, ceilA, ceilB, ceilC, ceilD.
  compute [balancedQ shallow_insert isSingleSize isBalancedSize shallow_singly_balanced].
  unfold Qlt_le_dec_bool.
  intuition.
  case (Qlt_le_dec (1 + 0) (ratio * (1 + ((e # 1))))).
  unfold Is_true.
  auto.
  intro f.
  compute.
  clear - H13 f H4.
  psatz Q.
  clear - H14 H13.
  psatzl Q.
  assert ((e # 1) + (2 # 1) + 1 > delta * ((a # 1) + 1)) as asmall.
  Focus.
  case (Qlt_le_dec (delta * ((a # 1) + 1)) ((e # 1) + (2 # 1) + 1)).
  auto.
  intro alarge.
  apply False_ind.
  apply H16.
  psatzl Q.
  split.
  psatzl Q.
  psatzl Q.
  Unfocus.
  clear - asmall H18 H1 H H15.
  psatz Q.
  psatzl Q.
  psatzl Q.
  assert ((e # 1) + (2 # 1) + 1 > delta * ((a # 1) + 1)) as asmall.
  Focus.
  case (Qlt_le_dec (delta * ((a # 1) + 1)) ((e # 1) + (2 # 1) + 1)).
  auto.
  intro alarge.
  apply False_ind.
  apply H16.
  psatzl Q.
  split.
  psatzl Q.
  psatzl Q.
  Unfocus.
  clear - H H1 H3 asmall H18 H15 H13.
  apply Qle_trans with
    ((((e # 1) + (3 # 1)) / delta) + 1).
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  apply Qle_trans with 0.
  intuition.
  psatzl Q.
  psatzl Q.
  eapply Qle_minus_iff.
  field_simplify.
  apply Qle_shift_div_l.
  psatzl Q.
  apply Qle_trans with 0.
  intuition.
  clear asmall H3.
  clear H18 H15.
  apply Qle_trans with
    (((e # 1) * (delta ^ 2 - 1)) + (delta ^ 2 - delta - (3 # 1))).
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  apply Qmult_le_0_compat.
  auto.
  psatzl Q.
  psatz Q.
  ring_simplify.
  intuition.
  psatzl Q.
  Qed.


Lemma NR_shallow_delete:
  good_params -> forall (a e: Z),
  shallow_delete isBalancedSize isSingleSize (a#1) (e#1).
  unfold good_params.
  unfold normal, slope, curve, deltasup, ceilA, ceilB, ceilC, ceilD.
  intuition.
  compute [shallow_delete balancedQ isSingleSize isBalancedSize shallow_singly_balanced].
  unfold Qlt_le_dec_bool.
  intuition.
  case (Qlt_le_dec (1 + 0) (ratio * (1 + (e # 1)))).
  unfold Is_true.
  auto.
  unfold Is_true.
  intro r_small.
  clear - r_small H4 H14.
  psatz Q.
  clear - H H8.
  psatz Q.
  case (Qlt_le_dec (delta * (0 + 1)) ((a # 1) + 1)).
  Focus 2.
  auto.
  Unfocus.
  intro a_large.
  apply False_ind.
  clear H5 H6 H7 H9.
  clear H10.
  clear H13 H11.
  psatz Q.
  psatzl Q.
  psatzl Q.
  assert (delta * ((a # 1) + 1) < 1 + (e # 1) + 1) as asmall.
  case (Qlt_le_dec (delta * ((a # 1) + 1)) (1 + (e # 1) + 1)).
  auto.
  intro e11.
  apply False_ind.
  apply H17.
  psatzl Q.
  psatzl Q.
  clear H16.
  clear H13.
  clear H10.
  clear H11.
  apply Qle_trans with
    ((((e # 1) + (2 # 1)) / delta) + 1).
clear - asmall H.
eapply Qle_minus_iff.
field_simplify.
apply Qle_shift_div_l.
psatzl Q.
apply Qle_trans with 0.
intuition.
psatz Q.
psatzl Q.
eapply Qle_minus_iff.
field_simplify.
apply Qle_shift_div_l.
psatzl Q.
apply Qle_trans with 0.
intuition.
clear H0 H4 H2 H5 H6 H7 H9.
apply Qle_trans with
  ((delta + 1) * ((e # 1) * (delta - 1) + (delta - (2 # 1)))).
apply Qmult_le_0_compat.
psatzl Q.
apply Qle_trans with (0 + 0).
intuition.
apply Qplus_le_compat.
apply Qmult_le_0_compat.
assumption.
assumption.
clear - H H1.
psatz Q.
ring_simplify.
intuition.
psatzl Q.
  Qed.

(* end of arithmetic lemmas *)

(*************************************************
   Part 2: program lemmas.
   insertion and deletion keep balance.
**************************************************)
Require Import OrderedType.

Module FSet (X: OrderedType).

(* FSet tree definitions and auxiliary functions *)
  
Definition Size := Z.

Section map.

Definition K := X.t.


Inductive FSet :=
| Tip: FSet
| Bin: Size -> K -> FSet -> FSet -> FSet.

Fixpoint size (m: FSet): Size :=
  match m with
    | Tip => 0%Z
    | Bin sz _ _ _ => sz
  end.

Open Scope Z_scope.

Definition bin: K -> FSet -> FSet -> FSet := 
  fun key l r =>
    Bin (1 + size l + size r) key l r.

Lemma bin_size: forall (x: K) (l r: FSet),
  (size (bin x l r) # 1) == 1 + (size l # 1) + (size r # 1).
intros x l r.
unfold bin.
unfold size.
fold size.
compute -[Zmult Zplus Zle Zlt size].
psatzl Z.
Qed.

End map.


Variable (deltaU deltaD: Z).
Axiom delta_eq: (deltaU # 1) == delta * (deltaD # 1).
Axiom deltaDnz: (deltaD # 1) > 0%Q.

Open Scope Z_scope.

Fixpoint realsize (t: FSet) :=
  match t with
    | Tip => 0
    | Bin sz _ l r =>
      1 + (realsize l) + (realsize r)
  end.

Definition Qrealsize (t: FSet) :Q :=
  (realsize t # 1).

Definition isBalancedSizeZ (x y:Size): bool:=
  Zle_bool (deltaD * (y + 1)) (deltaU * (x + 1)).

(* the proof begins *)

Lemma S_NR_isBalancedSize:
  forall x y: Size,
    Is_true (isBalancedSizeZ x y) <-> isBalancedSize (x # 1) (y # 1).
  intros x y.
  unfold isBalancedSizeZ.
  unfold isBalancedSize.
  apply iff_trans with ((deltaD * (y + 1)) <= (deltaU * (x + 1))).
  case_eq (Zle_bool (deltaD * (y + 1)) (deltaU * (x + 1))).
  intro zle.
  unfold Is_true.
  unfold iff.
  split.
  intro.
  apply Zle_bool_imp_le.
  assumption.
  auto.
  intro zle.
  unfold Is_true.
  split.
  intro f.
  apply False_ind.
  assumption.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite le in zle.
  generalize zle.
  discriminate.
  Open Scope Q_scope.
  apply iff_trans with ((deltaD # 1) * ((y # 1) + 1) <= ((deltaU # 1) * ((x # 1)  + 1))).
  compute -[Zmult Zplus Zle Zlt].
  psatzl Z.
  generalize delta_eq.
  intro eq.
  rewrite eq.
  clear eq.
  generalize deltaDnz.
  intro ddnz.
  generalize dependent ((y # 1) + 1).
  generalize dependent ((x # 1) + 1).
  clear x y.
  intros x y.
  split.
  intro ano.
  psatz Q.
  intuition.
  psatz Q.
  Qed.

Definition isBalanced (l r:FSet): bool :=
  isBalancedSizeZ (size l) (size r).

Lemma S_NRisBalanced : forall (l r: FSet),
  Is_true (isBalanced l r) <-> isBalancedSize ((size l) # 1) ((size r) # 1).
  unfold isBalanced.
  intros l r.
  apply S_NR_isBalancedSize.
  Qed.

Lemma realsize_nneg: forall t: FSet,
  0 <= (realsize t) # 1.
  induction t.
  unfold realsize.
  intuition.
  unfold realsize.
  fold realsize.
  apply Qle_trans with
    ((1 # 1) + (realsize t1 # 1) + (realsize t2 # 1)).
  psatz Q.
  clear.
  compute -[Zmult Zle Zlt Zplus].
  intuition.
  Qed.

Definition validsize : FSet -> Prop :=
  fun t => (realsize t) = (size t).

Lemma size_nneg: forall t: FSet,
  validsize t ->
  0 <= (size t) # 1.
  intro t.
  unfold validsize.
  intro rs.
  rewrite <- rs.
  apply realsize_nneg.
  Qed.


Variable (ratioU ratioD: Z).
Axiom ratio_eq: (ratioU # 1) == ratio * (ratioD # 1).
Axiom ratioDnneg: (ratioD # 1) > 0.

Definition isSingleSizeP (x y:Size): bool:=
  Zgt_bool (ratioU * (y + 1)) (ratioD * (x + 1)) .

Lemma NR_SisSingleSize: forall (x y: Size),
  isSingleSizeP x y = isSingleSize (x # 1) (y # 1).
  intros x y.
  unfold isSingleSizeP.
  unfold isSingleSize.
  unfold Qlt_le_dec_bool.
  case (Qlt_le_dec (1 + (x # 1)) (ratio * (1 + (y # 1)))).
  intro lt.
  case (Z_gt_le_dec (ratioU * (y + 1)) (ratioD * (x + 1))).
  eapply Zgt_is_gt_bool.
  intro le.
  apply False_ind.
  generalize ratio_eq.
  assert (((ratioU # 1) * ((y # 1) + 1) <= (ratioD # 1) * ((x # 1) + 1))) as leQ.
  clear - le.
  compute -[Zle Zlt Zmult Zplus].
  psatz Z.
  clear le.
  intro eq.
  rewrite eq in leQ.
  clear eq.
  generalize ratioDnneg.
  intro nneg.
  psatz Q.
  intro rsmall.
  Open Scope Z_scope.
  assert ((ratioU * (y + 1)) <= (ratioD * (x + 1))).
  Close Scope Z_scope.
  assert ((ratioU # 1) * ((y # 1) + 1) <= (ratioD # 1) * ((x # 1) + 1)).
  rewrite ratio_eq.
  generalize ratioDnneg.
  psatz Q.
  clear rsmall.
  generalize H.
  clear H.
  compute -[Zle Zlt Zmult Zplus].
  psatzl Z.
  clear rsmall.
  case_eq (Zgt_bool (ratioU * (y + 1)) (ratioD * (x + 1))).
  intro f.
  apply False_ind.
  eapply Zgt_is_gt_bool in f.
  intuition.
  auto.
  Qed.

Definition isSingle (l r:FSet): bool :=
  isSingleSizeP (size l) (size r).

Lemma NR_SisSingle: forall (l r: FSet),
  isSingle l r =
  isSingleSize ((size l) # 1) ((size r) # 1).
  intros l r.
  unfold isSingle.
  apply NR_SisSingleSize.
  Qed.

Fixpoint balanced (t: FSet): bool :=
  match t with
    | Tip => true
    | Bin _ _ l r =>
      (isBalanced l r && isBalanced r l && balanced l && balanced r)
  end.

Fixpoint NRbalanced (t: FSet): Prop :=
  match t with
    | Tip => True
    | Bin _ _ l r =>
      balancedQ isBalancedSize (size l # 1) (size r # 1)
      /\ NRbalanced l /\ NRbalanced r
  end.

Definition assert_false := bin.

Definition doubleL : K -> FSet -> FSet -> FSet :=
  fun k1 t1 t2 =>
    match t2 with
      | Bin _ k2 (Bin _ k3 t2 t3) t4 =>
        bin k3 (bin k1 t1 t2) (bin k2 t3 t4)
      | _ => assert_false k1 t1 t2 
    end.

Open Scope Z_scope.

Lemma realsize_bin:
  forall (k0: K) (l r: FSet),
   realsize (bin k0 l r) = 1 + realsize l + realsize r.
  auto.
  Qed.


  Lemma size_bin:
    forall (kx: K) (l r: FSet),
      (size (bin kx l r) # 1) == 1 + (size l # 1) + (size r # 1).
    intros kx l r.
    unfold bin.
    unfold size.
    fold size.
  compute -[Zmult Zplus Zle Zlt size].
psatzl Z.
    Qed.

    Hint Rewrite realsize_bin size_bin: sbin.

Lemma validsize_realsize_size:
  forall (l: FSet),
     (validsize l) ->
    realsize l = size l.
  compute [validsize].
  auto.
   Qed.
 
Fixpoint validsize_rec (t: FSet): Prop :=
  match t with
    | Tip =>   validsize t 
    | Bin _ _ l r =>
        validsize t /\ validsize_rec l /\ validsize_rec r
  end.

Lemma validsize_rec_tip:
  validsize_rec Tip.
  compute.
  intuition.
Qed.

Lemma validsize_rec_hereditary1:
  forall (s: Size) (k0: K) (l1 l2: FSet),
     (validsize_rec (Bin s k0 l1 l2)) ->
     (validsize_rec l1).
  intros s k0 a0 l1 l2.
  unfold validsize_rec in l2.
  intuition.
  Qed.

Lemma validsize_rec_hereditary2:
  forall (s: Size) (k0: K) (l1 l2: FSet),
    (validsize_rec (Bin s k0 l1 l2)) ->
    (validsize_rec l2).
  intros s k0 l1 l2.
  unfold validsize_rec.
  intuition.
  Qed.
  
Lemma validsize_rec_self:
  forall (m: FSet),
     (validsize_rec m) ->
     (validsize m).
  intro m.
  destruct m.
  intuition.
  unfold validsize_rec.
  intuition.
  Qed.

Lemma validsize_rec_bin:
  forall (kx : K) (l r : FSet),
    (validsize_rec l) ->  (validsize_rec r) ->
     (validsize_rec (bin kx l r)).
  intros kx l r lval rval.
  unfold bin.
  unfold validsize_rec.
  intuition.
  apply validsize_rec_self in lval.
  apply validsize_rec_self in rval.
  unfold validsize in *.
  unfold realsize.
  unfold size.
  intuition.
  Qed.

Lemma validsize_rec_expand:
  forall (kx: K) (l r:FSet),
    (validsize_rec (bin kx l r) = (validsize (bin kx l r) /\ validsize_rec l /\ validsize_rec r)).
  intros.
  unfold bin.
  unfold validsize_rec.
  fold validsize_rec.
  intuition.
  Qed.

Lemma validsize_rec_expand_prop:
  forall (kx: K) (l r:FSet),
     (validsize (bin kx l r)) ->
     (validsize_rec l) ->
     (validsize_rec r) ->
     (validsize_rec (bin kx l r)).
intros kx l r.
rewrite validsize_rec_expand.
unfold bin.
unfold validsize.
unfold realsize.
unfold size.
intuition.
  Qed.

  Hint Resolve
    validsize_rec_bin
    validsize_rec_self validsize_rec_hereditary1 validsize_rec_hereditary2.

Lemma doubleL_size:
  forall (x:K) (t1 t2: FSet),
    validsize_rec t1 -> validsize_rec t2 ->
    (size (doubleL x t1 t2) # 1) ==
    1 + (size t1 # 1) + (size t2 # 1).
  intros x t1 t2.
  unfold doubleL.
  case_eq t2.
  intro t2tip.
  rewrite <- t2tip.
  unfold assert_false.
  rewrite bin_size.
  intuition.
  intros s y f1 f2.
  intro t2bin.
  rewrite <- t2bin.
  case_eq f1.
  intro f1tip.
  unfold assert_false.
  rewrite bin_size.
  intuition.
  intro xs.
  intros z f3 f4.
  intro f1bin.
  intro vrect1.
  intro vrect2.
  rewrite t2bin.
  rewrite f1bin.
  rewrite bin_size.
  rewrite bin_size.
  rewrite bin_size.
  unfold size.
  fold size.
  assert (validsize_rec t2) as vrect2_1.
  assumption.
  rewrite t2bin in vrect2.
  apply validsize_rec_self in vrect2.
  unfold validsize in vrect2.
  unfold size in vrect2.
  rewrite <- vrect2.
  clear vrect2.
  unfold realsize.
  fold realsize.
  assert (realsize f1 = size f1).
  rewrite t2bin in vrect2_1.
  unfold validsize_rec in vrect2_1.
  fold validsize_rec in vrect2_1.
  intuition.
  apply validsize_rec_self in H1.
  unfold validsize in H1.
  auto.
  rewrite H.
  replace (realsize f2) with (size f2).
  compute -[size Zmult Zplus Zle Zlt].
  ring_simplify.
  replace (size f1) with (realsize f1).
  replace (realsize f1) with ((realsize f3) + (realsize f4) + 1).
  replace (realsize f3) with (size f3).
  replace (realsize f4) with (size f4).
  ring_simplify.
  intuition.
  clear H.
  rewrite f1bin in t2bin.
  clear f1bin.
  rewrite t2bin in vrect2_1.
  clear t2bin.
  unfold validsize_rec in vrect2_1.
  fold validsize_rec in vrect2_1.
  intuition.
  apply validsize_rec_self in H4.
  unfold validsize in H4.
  rewrite H4.
  reflexivity.
  rewrite t2bin in vrect2_1.
  rewrite f1bin in vrect2_1.
  unfold validsize_rec in vrect2_1.
  fold validsize_rec in vrect2_1.
  intuition.
  apply validsize_rec_self in H2.
  unfold validsize in H2.
  rewrite H2.
  reflexivity.
  rewrite f1bin.
  unfold realsize.
  intuition.
  rewrite t2bin in vrect2_1.
  rewrite f1bin in vrect2_1.
  unfold validsize_rec in vrect2_1.
  fold validsize_rec in vrect2_1.
  intuition.
  apply validsize_rec_self in H3.
  unfold validsize in H3.
  rewrite H3.
  reflexivity.
  Qed.
  

Definition singleL : K -> FSet -> FSet -> FSet :=
  fun k1 t1 t2 =>
    match t2 with
      | (Bin _ k2 t2 t3)  => bin k2 (bin k1 t1 t2) t3
      | _ => assert_false k1 t1 t2
    end.

Lemma singleL_size:
  forall (x: K) (t1 t2: FSet),
    validsize_rec t1 -> validsize_rec t2 ->
    (size (singleL x t1 t2) # 1) == 1 + (size t1 # 1) + (size t2 # 1).
  intros x t1 t2.
  intros vrect1 vrect2.
  unfold singleL.
  destruct t2.
  unfold assert_false.
  rewrite size_bin.
  clear.
  compute -[Zmult Zplus size Zle Zlt].
  psatzl Z.
  rewrite size_bin.
  rewrite size_bin.
  unfold size.
  fold size.
  replace s with (size t2_1 + size t2_2 + 1).
  compute -[Zmult Zplus size Zle Zlt].
  psatzl Z.
  replace s with (realsize (Bin s k t2_1 t2_2)).
  Focus 2.
  apply validsize_rec_self in vrect2.
  unfold validsize in vrect2.
  unfold size in vrect2.
  assumption.
  Unfocus.
  replace (size t2_1) with (realsize t2_1).
  replace (size t2_2) with (realsize t2_2).
  unfold realsize.
  fold realsize.
  psatzl Z.
  apply validsize_rec_hereditary2 in vrect2.
  apply validsize_rec_self in vrect2.
  unfold validsize in vrect2.
  assumption.
  apply validsize_rec_hereditary1 in vrect2.
  apply validsize_rec_self in vrect2.
  unfold validsize in vrect2.
  assumption.
  Qed.
  

Definition rotateL : K -> FSet -> FSet -> FSet :=
  fun k l r =>
    match r with
      | Tip => assert_false k l r
      | Bin _ _ rl rr =>
        if isSingle rl rr then
          singleL k l r
        else
          doubleL k l r
    end.

Lemma rotateL_size :
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    (size (rotateL x l r) # 1) ==
    1 + (size l # 1) + (size r # 1).
  intros x l r.
  intros vrecl vrecr.
  unfold rotateL.
  destruct r.
  unfold assert_false.
  rewrite size_bin.
  compute -[Zmult Zplus Zle Zlt size].
  psatzl Z.
  case (isSingle r1 r2).
  rewrite singleL_size.
  intuition.
  assumption.
  assumption.
  rewrite doubleL_size.
  intuition.
  auto.
  auto.
  Qed.
  

Lemma rotateL_sizeZ :
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    (size (rotateL x l r)) =
    1 + (size l) + (size r).
  intros.
  generalize (rotateL_size x l r).
  intro.
  apply H1 in H.
  generalize H.
  clear.
  compute -[Zmult Zplus Zle Zlt size rotateL].
  psatzl Z.
  eauto.
  Qed.

Definition balanceL: K -> FSet -> FSet -> FSet :=
  fun k l r =>
    match (isBalanced l r) with
      | true => bin k l r
      | false => rotateL k l r
    end.

Lemma size_balanceL:
  forall (x: K) (l r : FSet),
    validsize_rec l -> validsize_rec r ->
    (size (balanceL x l r) # 1) ==
    1 + (size l # 1) + (size r # 1).
  intros x l r.
  intros vrecl vrecr.
  unfold balanceL.
  case (isBalanced l r).
  rewrite size_bin.
  clear.
  compute -[size Zmult Zle Zplus Zlt].
  psatzl Z.
  rewrite rotateL_size.
  intuition.
  auto.
  auto.
  Qed.

Definition doubleR : K -> FSet -> FSet -> FSet :=
  fun k1 t t4 =>
    match t with
      | (Bin _ k2 t1 (Bin _ k3 t2 t3)) =>
        bin k3 (bin k2 t1 t2) (bin k1 t3 t4)
      | _ => assert_false k1 t t4
    end.

Lemma size_doubleR :
  forall (x: K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    (size (doubleR x l r) # 1) ==
    1 + (size l # 1) + (size r # 1).
  intros x l r.
  unfold doubleR.
  destruct l.
  unfold assert_false.
  rewrite size_bin.
  compute -[Zmult Zle Zplus Zlt size].
  psatzl Z.
  destruct l2.
  unfold assert_false.
  rewrite size_bin.
  compute -[Zmult Zle Zplus Zlt size].
  psatzl Z.
  rewrite size_bin.
  rewrite size_bin.
  rewrite size_bin.
  intro vrecB.
  intro vrecr.
  unfold size.
  fold size.
  replace s with (realsize (Bin s k l1 (Bin s0 k0 l2_1 l2_2))).
  unfold realsize.
  fold realsize.
  replace (realsize l1) with (size l1).
  replace (realsize l2_1) with (size l2_1).
  replace (realsize l2_2) with (size l2_2).
  compute -[Zmult Zplus Zle Zlt size].
  psatzl Z.
  apply validsize_rec_hereditary2 in vrecB.
  apply validsize_rec_hereditary2 in vrecB.
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  rewrite vrecB.
  reflexivity.
  apply validsize_rec_hereditary2 in vrecB.
  apply validsize_rec_hereditary1 in vrecB.
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  rewrite vrecB.
  reflexivity.
  apply validsize_rec_hereditary1 in vrecB.
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  rewrite vrecB.
  reflexivity.
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  unfold size in vrecB.
  assumption.
  Qed.

Definition singleR : K -> FSet -> FSet -> FSet :=
  fun k1 t t3 =>
    match t with
      | (Bin _ k2 t1 t2) => bin k2 t1 (bin k1 t2 t3)
      | _ => assert_false k1 t t3
    end.

Lemma size_singleR:
  forall (x: K) (l r : FSet),
    validsize_rec l -> validsize_rec r ->
    (size (singleR x l r) # 1) ==
    1 + (size l # 1) + (size r # 1).
  intros x l r.
  unfold singleR.
  destruct l.
  unfold assert_false.
  rewrite size_bin.
  intros.
  intuition.
  intros vrecB vrecr.
  rewrite size_bin.
  rewrite size_bin.
  unfold size.
  fold size.
  replace s with (1 + size l1 + size l2).
  compute -[Zmult Zle Zplus Zlt size].
  psatzl Z.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  unfold size in vrecB.
  rewrite <- vrecB.
  unfold realsize.
  fold realsize.
  intuition.
  apply validsize_rec_hereditary2 in vrecB.
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  assumption.
  apply validsize_rec_hereditary1 in vrecB.
  apply validsize_rec_self in vrecB.
  unfold validsize in vrecB.
  assumption.
  Qed.

Definition rotateR : K -> FSet -> FSet -> FSet :=
  fun k l r =>
    match l with
      | Tip => assert_false k l r
      | Bin _ _ ll lr =>
        if isSingle lr ll then
          singleR k l r
        else 
          doubleR k l r
    end.

Lemma size_rotateR:
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    (size (rotateR x l r) # 1) ==
    1 + (size l # 1) + (size r # 1).
  intros x l r.
  unfold rotateR.
  destruct l.
  unfold assert_false.
  rewrite size_bin.
  intuition.
  case (isSingle l2 l1).
  intros.
  rewrite size_singleR.
  intuition.
  auto.
  auto.
  intros.
  rewrite size_doubleR.
  intuition.
  auto.
  auto.
  Qed.
  

Definition balanceR (kx: K) (l r:FSet) :=
  match (isBalanced r l) with
    | true => bin kx l r
    | false => rotateR kx l r
  end.

Lemma size_balanceR:
  forall (x: K) (l r :FSet),
    validsize_rec l -> validsize_rec r ->
    (size (balanceR x l r) # 1) ==
    1 + (size l # 1) + (size r # 1).
  intros x l r.
  intros vrecl vrecr.
  unfold balanceR.
  case (isBalanced r l).
  rewrite size_bin.
  intuition.
  rewrite size_rotateR.
  intuition.
  auto.
  auto.
  Qed.

Open Scope Z_scope.

Definition singleton (kx: K) :=
  Bin 1 kx Tip Tip.


Fixpoint insert (kx:K) (t:FSet): FSet :=
  match t with
    | Tip => singleton kx
    | Bin _ ky l r =>
      match X.compare kx ky with
        | GT _ => balanceL ky l (insert kx r)
        | LT _ => balanceR ky (insert kx l) r
        | EQ _ => bin kx l r
      end
  end.

  

Lemma validsize_bin:
  forall (kx : K) (l r : FSet),
     (validsize l) -> (validsize r) ->
     (validsize (bin kx l r)).
  intros kx l r.
  compute [validsize].
  intros lvalid rvalid.
  unfold bin.
  unfold realsize.
  fold realsize.
  unfold size.
  fold size.
  psatzl Z.
  Qed.


Lemma validsize_singleR:
  forall (kx: K) (l r: FSet),
     (validsize_rec l) ->
     (validsize_rec r) ->
     (validsize_rec (singleR kx l r)).
  intros kx l r.
  unfold singleR.
  case l.
  eauto.
  eauto.
Qed.

Lemma validsize_singleL:
  forall (kx: K) (l r: FSet),
     (validsize_rec l) ->
     (validsize_rec r) ->
     (validsize_rec (singleL kx l r)).
  intros kx l r.
  destruct r.
  unfold singleL.
  unfold assert_false.
  eauto.
  unfold singleL.
  eauto.
Qed.

Lemma validsize_doubleR:
  forall (t t4: FSet) (k1: K),
     (validsize_rec t) ->
     (validsize_rec t4) ->
     (validsize_rec (doubleR k1 t t4)).
intros l r kx.
unfold doubleR.
destruct l.
unfold assert_false.
eauto.
destruct l2.
unfold assert_false.
eauto.
intros.
unfold validsize_rec in H.
fold validsize_rec in H.
intuition.
Qed.

Lemma validsize_doubleL:
  forall (t t4: FSet)
    (k1: K),
     (validsize_rec t) ->
     (validsize_rec t4) ->
     (validsize_rec (doubleL k1 t t4)).
  intros  t t4 k1.
  intros tval val4.
  compute [doubleL].
  destruct t4.
  eauto.
  destruct t4_1.
  eauto.
  apply validsize_rec_bin.
  eauto.
  eauto.
  Qed.

  
Lemma validsize_balanceR:
  forall (kx: K) (l r: FSet),
    (validsize_rec l) ->
    (validsize_rec r) ->
    (validsize_rec (balanceR kx l r)).
  intros kx l r.
  intros vl vr.
  compute [balanceR].
  case (isBalanced r l).
  auto.
  compute [rotateR].
  destruct l.
  auto.
  case (isSingle l2 l1).
  apply validsize_singleR.
  auto.
  auto.
  apply validsize_doubleR.
  auto.
  auto.
  Qed.

Lemma validsize_balanceL:
  forall (kx: K) (l r: FSet),
     (validsize_rec l) ->
     (validsize_rec r) ->
     (validsize_rec (balanceL kx l r)).
  intros kx l r.
  intros vl vr.
  compute [balanceL].
  case (isBalanced l r).
  auto.
  compute [rotateL].
  destruct r.
  auto.
  case (isSingle r1 r2).
  apply validsize_singleL.
  intuition.
  intuition.
  apply validsize_doubleL.
  intuition.
  intuition.
  Qed.

Lemma validsize_insert:
  forall (t: FSet) (kx: K),
     (validsize_rec t) ->
     (validsize_rec (insert kx t)).
intros t kx.
induction t.
intro pre.
simpl.
intuition.
compute.
intuition.
intro pre.
simpl.
case (X.compare kx k).
intro irr.
clear irr.
apply validsize_balanceR.
apply IHt1.
eauto.
eauto.
intro irr.
clear irr.
eauto.
intro irr.
clear irr.
apply validsize_balanceL.
eauto.
eauto.
Qed.

Open Scope Q_scope.

Lemma val_sizeBin:
  forall (t1 t2: FSet) (s: Size) (k0: K),
    validsize_rec (Bin s k0 t1 t2) ->
    1 + (size t1 # 1) + (size t2 # 1) == size (Bin s k0 t1 t2) # 1.
  intros t1 t2 s x.
  intro vrec.
  unfold size.
  fold size.
  replace (size t1) with (realsize t1).
  replace (size t2) with (realsize t2).
  replace s with (realsize (Bin s x t1 t2)).
  unfold realsize.
  fold realsize.
  compute -[Zle Zlt Zplus Zmult realsize].
  psatzl Z.
  assert (validsize (Bin s x t1 t2)).
  eauto.
  unfold validsize in H.
  rewrite H.
  unfold size.
  reflexivity.
  assert (validsize t2).
  eauto.
  unfold validsize in H.
  auto.
  assert (validsize t1).
  eauto.
  unfold validsize in H.
  auto.
  Qed.


Lemma size_insert:
  forall (x:K) (t:FSet),
  validsize_rec t ->
  ((size (insert x t) # 1) == 1 + ((size t) # 1)
    \/
    (size (insert x t) # 1) == ((size t) # 1)).
  intros x t.
  intro vrec.
  unfold insert.
  induction t.
  intuition.
  case (X.compare x k).
  intro lt.
  clear lt.
  rewrite size_balanceR.
  fold insert.
  fold insert in IHt1.
  clear IHt2.
  elim IHt1.
  intuition.
  Focus 2.
  intro eq.
  right.
  rewrite eq.
  apply val_sizeBin.
  auto.
  Unfocus.
  left.
  rewrite H.
  rewrite <- val_sizeBin.
  psatzl Q.
  eauto.
  eauto.
  fold insert.
  apply validsize_insert.
  eauto.
  eauto.
  intro eq.
  right.
  rewrite size_bin.
  apply val_sizeBin.
  eauto.
  intro lt.
  fold insert in *.
  clear IHt1.
  assert (validsize_rec t2).
  eauto.
  apply IHt2 in H.
  clear IHt2.
  destruct H.
  Focus 2.
  right.
  rewrite size_balanceL.
  rewrite H.
  rewrite val_sizeBin.
  intuition.
  eauto.
  eauto.
  apply validsize_insert.
  eauto.
  Unfocus.
  left.
  rewrite size_balanceL.
  rewrite H.
  rewrite <- val_sizeBin.
  psatzl Q.
  auto.
  eauto.
  apply validsize_insert.
  eauto.
  Qed.
  
  
Lemma NR_S_balanced:
  forall t: FSet,
    validsize_rec t ->
    (NRbalanced t <-> Is_true (balanced t)).
  intro t.
  induction t.
  compute.
  intuition.
  unfold validsize_rec.
  fold validsize_rec.
  unfold NRbalanced.
  fold NRbalanced.
  unfold balanced.
  fold balanced.
  intuition.
  unfold isBalanced.
  assert (Is_true (isBalancedSizeZ (size t1) (size t2))).
  eapply S_NR_isBalancedSize.
  unfold balancedQ in H7.
  intuition.
  assert (Is_true (isBalancedSizeZ (size t2) (size t1))).
  unfold balancedQ in H7.
  eapply S_NR_isBalancedSize.
  intuition.
  repeat apply andb_prop_intro; split; intuition.
  unfold balancedQ.
  intuition.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  eapply S_NR_isBalancedSize.
  unfold isBalanced in H1.
  clear - H1.
  apply andb_prop_elim in H1; intuition.
  apply andb_prop_elim in H; intuition.
  apply andb_prop_elim in H1; intuition.
  eapply S_NR_isBalancedSize.
  apply andb_prop_elim in H1; intuition.
  apply andb_prop_elim in H7; intuition.
  apply andb_prop_elim in H5; intuition.
  apply H4.
  unfold balanced.
  destruct t1.
  intuition.
  fold balanced.
  apply andb_prop_elim in H1; intuition.
  apply andb_prop_elim in H7; intuition.
  apply andb_prop_elim in H1; intuition.
  Qed.

Hint Resolve NR_S_balanced.

Close Scope Q_scope.

Lemma tip_one_balance:
  forall (s : Size) (k0 : K) (t1 : FSet) (kx : K), 
  good_params ->
  validsize_rec (Bin s k0 t1 Tip) ->
  Is_true (balanced (Bin s k0 t1 Tip)) ->
  Is_true (isBalanced t1 (Bin 1 kx Tip Tip)).
  intros s k0 t k1.
  intro gp.
  intro vrec.
  intro sb.
  assert (NRbalanced (Bin s k0 t Tip)) as nrb.
  eapply NR_S_balanced.
  assumption.
  assumption.
  clear sb.
  assert (isBalancedSize ((size t) # 1) ((size (Bin 1 k1 Tip Tip)) # 1)).
  Focus 2.
  eapply S_NRisBalanced.
  assumption.
  Unfocus.
  unfold isBalancedSize.
  unfold size.
  fold size.
  unfold NRbalanced in nrb.
  fold NRbalanced in nrb.
  intuition.
  unfold good_params in gp.
  intuition.
  unfold balancedQ in H.
  intuition.
  clear H.
  unfold normal in H0.
  intuition.
  clear H2.
  clear H1.
  clear vrec.
  clear H14.
  clear H13.
  clear H11.
  clear - H9 H H0.
  psatz Q.
  Qed.
  

Lemma right_tip_insert:
  forall (s : Size) (k0 : K) (t1 : FSet) (kx : K),
    good_params -> Is_true (balanced (Bin s k0 t1 Tip)) -> validsize_rec (Bin s k0 t1 Tip) ->
    Is_true (balanced (balanceL k0 t1 (singleton kx))).
  intros s k0 t1 kx.
  unfold good_params.
  unfold normal, slope, curve, deltasup, ceilA, ceilB, ceilC, ceilD.
  intro gp.
  unfold singleton.
  unfold balanceL.
  intro tbalance.
  intro vrec.
  assert (Is_true (isBalanced t1 (Bin 1 kx Tip Tip))).
  eapply tip_one_balance.
  unfold good_params.
  split.
  unfold normal.
  intuition.
  unfold slope; intuition.
  apply vrec.
  assumption.
  case_eq (isBalanced t1 (Bin 1 kx Tip Tip) ).
  intro t.
  unfold balanced.
  unfold bin.
  apply andb_prop_intro; intuition.
  apply andb_prop_intro; intuition.
  apply andb_prop_intro; intuition.
  eapply S_NRisBalanced.
  unfold isBalancedSize.
  unfold size.
  fold size.
  unfold balanced in tbalance.
  apply andb_prop_elim in tbalance.
  intuition.
  apply andb_prop_elim in H9.
  intuition.
  apply andb_prop_elim in H12.
  intuition.
  clear H11 H13.
  eapply S_NRisBalanced in H9.
  eapply S_NRisBalanced in H14.
  unfold isBalancedSize in H9.
  clear H9.
  unfold isBalancedSize in H14.
  unfold size in H14.
  fold size in H14.
  clear - H14 H2.
  psatzl Q.
  fold balanced.
  unfold balanced in tbalance.
  apply andb_prop_elim in tbalance; intuition.
  apply andb_prop_elim in H9; intuition.
  apply andb_prop_intro; intuition.
  apply andb_prop_intro; intuition.
  apply andb_prop_intro; intuition.
  unfold isBalanced.
  unfold size.
  eapply S_NR_isBalancedSize.
  unfold isBalancedSize.
  clear - H2.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold isBalancedSize.
  unfold size.
  clear - H2.
  psatzl Q.
  intro f.
  apply False_ind.
  rewrite f in H.
  generalize H.
  compute.
  auto.
  Qed.


Lemma validsize_rec_symm:
  forall (s: Size) (k0: K) (t2: FSet),
    validsize_rec (Bin s k0 Tip t2) ->
    validsize_rec (Bin s k0 t2 Tip).
  unfold validsize_rec.
  intuition.
  clear - H0.
  unfold validsize in *.
  unfold size in *.
  unfold realsize in *.
  fold realsize in *.
  psatzl Z.
  Qed.

Lemma balanced_symm:
  forall (s: Size) (k0: K) (t2: FSet),
    balanced (Bin s k0 Tip t2) = balanced (Bin s k0 t2 Tip).
  intros s x t.
  unfold balanced.
  fold balanced.
  case (balanced t); case (isBalanced Tip t); case (isBalanced t Tip); intuition.
  Qed.

Lemma insert_result_non_tip:
  forall (t: FSet) (x: K),
    insert x t = Tip -> False.
  intros t x.
  induction t.
  unfold insert.
  unfold singleton.
  discriminate.
  unfold insert.
  fold insert.
  case (X.compare x k).
  Focus 2.
  unfold bin.
  intro.
  discriminate.
  Unfocus.
  intro.
  unfold balanceR.
  unfold rotateR.
  unfold doubleR.
  unfold singleR.
  case (isBalanced t2 (insert x t1)).
  unfold bin.
  discriminate.
  destruct (insert x t1).
  apply False_ind.
  apply IHt1.
  trivial.
  case (isSingle f2 f1).
  Focus 2.
  destruct f2.
  unfold assert_false.
  unfold bin.
  discriminate.
  unfold bin.
  discriminate.
  unfold bin.
  discriminate.
  intro lt.
  unfold balanceL.
  case (isBalanced t1 (insert x t2)).
  unfold bin.
  discriminate.
  unfold rotateL.
  destruct (insert x t2).
  apply False_ind.
  apply IHt2.
  trivial.
  case (isSingle f1 f2).
  Focus 2.
  unfold doubleL.
  case f1.
  unfold assert_false.
  unfold bin.
  discriminate.
  intros.
  generalize H.
  unfold bin.
  discriminate.
  unfold singleL.
  unfold bin.
  discriminate.
  Qed.

Open Scope Q_scope.
  
Lemma zero_tip:
  forall (t1 : FSet),
    validsize t1 ->
    size t1 # 1 == 0 -> t1 = Tip.
  intro t1.
  intro vsize.
  unfold validsize in vsize.
  rewrite <- vsize.
  intro r0.
  destruct t1.
  reflexivity.
  unfold realsize in r0.
  fold realsize in r0.
  assert (0 <= realsize t1_1 # 1).
  apply realsize_nneg.
  assert (0 <= realsize t1_2 # 1).
  apply realsize_nneg.
  apply False_ind.
  clear - r0 H H0.
  generalize r0 H H0.
  compute -[realsize Zmult Zplus Zlt Zle].
  psatzl Z.
  Qed.
  

Hint Resolve andb_prop_intro andb_prop_elim.

Lemma TipTipBal:
  good_params ->
  Is_true (isBalanced Tip Tip).
  intro gp.
  eapply S_NRisBalanced.
  unfold size.
  unfold isBalancedSize.
  unfold good_params in gp.
  unfold normal in gp.
  psatzl Q.
  Qed.

Lemma bunsi_distr:
  forall (a b: Z),
    (a + b # 1) == (a # 1) + (b # 1).
  intros a b.
  compute -[Zmult Zplus Zle Zlt].
  psatzl Z.
  Qed.

Hint Rewrite bunsi_distr: bunsu.

Close Scope Q_scope.

Lemma size_size_size:
  forall (s1: Size) (k2: K) (eT1 eT2: FSet),
    validsize_rec (Bin s1 k2 eT1 eT2) ->
    1 + size eT1 + size eT2 = s1.
  intros s x t1 t2.
  intro vrec.
  replace (size t1) with (realsize t1).
  replace (size t2) with (realsize t2).
  apply validsize_rec_self in vrec.
  unfold validsize in vrec.
  unfold realsize, size in vrec.
  fold realsize in vrec.
  assumption.
  assert (validsize t2).
  eauto.
  unfold validsize in H.
  assumption.
  assert (validsize t1).
  eauto.
  unfold validsize in H.
  assumption.
  Qed.
  

Lemma insert_balanced:
  forall (t: FSet) (k: K),
    good_params ->
    Is_true (balanced t) -> validsize_rec t ->
    Is_true (balanced (insert k t)).
intros t x.
intro gp.
intro pre.
intro vrec.
unfold insert.
induction t.
unfold balanced.
unfold singleton.
apply andb_prop_intro; intuition.
apply andb_prop_intro; intuition.
apply andb_prop_intro; intuition.
clear pre.
eapply S_NRisBalanced.
unfold isBalancedSize.
unfold good_params in gp.
unfold normal in gp.
intuition.
unfold size.
psatzl Q.
eapply S_NRisBalanced.
unfold isBalancedSize.
unfold size.
unfold good_params in *.
unfold normal in *.
intuition.
psatzl Q.
case (X.compare x k).
intro lt.
clear lt.
fold insert.
case_eq (insert x t1).
intro tip.
apply False_ind.
eapply insert_result_non_tip.
apply tip.
intro s0.
intro k1.
intros eT cdT.
intro t1b.
case_eq cdT.
intro cdTtip.
rewrite cdTtip in *.
clear cdTtip.
fold insert in IHt1.
fold insert in IHt2.
generalize (size_insert x t1).
intro sizet1.
assert (validsize_rec t1).
eauto.
apply sizet1 in H.
clear sizet1.
destruct H as [sizeT1 | sizeT1].
unfold balanceR.
case_eq (
  isBalanced t2 (Bin s0 k1 eT Tip)).
intro bal.
unfold bin.
unfold balanced.
fold balanced.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H; intuition.
assert (Is_true (balanced (insert x t1))).
apply H.
eauto.
rewrite t1b in H4.
unfold balanced in H4.
apply andb_prop_elim in H4; intuition.
clear H6.
apply andb_prop_elim in H5; intuition.
apply andb_prop_elim in H4; intuition.
fold balanced in H6.
apply andb_prop_elim in H2; intuition.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
unfold isBalancedSize.
eapply S_NRisBalanced in H4.
unfold isBalancedSize in H4.
Open Scope Q_scope.
apply Qle_trans with
  (delta * ((size t1 # 1) + 1)).
assumption.
apply Qmult_le_compat_l.
rewrite <- t1b.
rewrite sizeT1.
psatzl Q.
clear - gp.
unfold good_params in *.
unfold normal in *.
psatzl Q.
(* now rotation occurrs *)
intro unbalance.
generalize NR_shallow_insert.
intro si.
intuition.
rename H into si.
Close Scope Q_scope.
elim si with (size t2) (size eT).
clear si.
intro single.
intro si.
unfold shallow_singly_balanced in si.
unfold balancedQ in si.
intuition.
unfold rotateR.
assert (Is_true (isSingle Tip eT)).
unfold isSingle.
unfold size.
fold size.
clear - single.
rewrite NR_SisSingleSize.
assumption.
case_eq (isSingle Tip eT).
Focus 2.
intro double.
rewrite double in H5.
apply False_ind.
clear - H5.
compute in H5.
auto.
Unfocus.
clear single.
intro single.
clear single.
clear H5.
unfold singleR.
unfold bin.
unfold balanced.
fold balanced.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre;intuition.
apply andb_prop_elim in H5;intuition.
apply andb_prop_elim in H10; intuition.
assert (Is_true (balanced (insert x t1))).
apply H5.
eauto.
rewrite t1b in H10.
unfold balanced in H10.
fold balanced in H10.
apply andb_prop_elim in H10; intuition.
apply andb_prop_elim in H14; intuition.
apply andb_prop_elim in H10; intuition.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
unfold size.
fold size.
clear - H7 gp.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr.
psatzl Q.
clear - H4 gp.
eapply S_NRisBalanced.
unfold size.
fold size.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
unfold balancedQ.
clear si.
assert (size eT = size t1).
rewrite t1b in sizeT1.
unfold size in sizeT1.
fold size in sizeT1.
Close Scope Q_scope.
assert (s0 = 1 + size t1).
clear - sizeT1.
compute -[Zmult Zle Zplus Zlt size] in sizeT1.
ring_simplify in sizeT1.
generalize dependent (size t1).
intro s.
intro q.
unfold Size in *.
psatzl Z.
clear sizeT1.
assert (validsize_rec (Bin s0 k1 eT Tip)).
rewrite <- t1b.
apply validsize_insert.
eauto.
assert (validsize (Bin s0 k1 eT Tip)).
eauto.
unfold validsize in H1.
unfold realsize in H1.
fold realsize in H1.
unfold size in H1.
rewrite H in H1.
clear H.
replace (size eT) with (realsize eT).
clear - H1.
generalize dependent (realsize eT).
generalize dependent (size t1).
intros s z.
unfold Size in *.
psatzl Z.
assert (validsize eT).
eauto.
unfold validsize in H.
trivial.
rewrite H.
intuition.
apply size_nneg.
eauto.
apply size_nneg.
eauto.
unfold isBalancedSize.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H0; intuition.
apply andb_prop_elim in H3; intuition.
eapply S_NRisBalanced in H6.
unfold isBalancedSize in H6.
assumption.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H0; intuition.
apply andb_prop_elim in H3; intuition.
eapply S_NRisBalanced in H5.
assumption.
unfold balancedQ.
assert (validsize_rec (insert x t1)).
apply validsize_insert.
eauto.
rewrite t1b in H.
intuition.
apply size_nneg.
eauto.
unfold isBalancedSize.
assert (Is_true (balanced (insert x t1))).
apply IHt1.
unfold balanced in pre.
apply andb_prop_elim in pre; intuition.
fold balanced in H0.
fold balanced in H1.
clear - H0.
apply andb_prop_elim in H0; intuition.
eauto.
rewrite t1b in H0.
apply andb_prop_elim in H0; intuition.
clear H2.
apply andb_prop_elim in H1; intuition.
clear H2.
apply andb_prop_elim in H0; intuition.
eapply S_NRisBalanced in H2.
unfold isBalancedSize in H2.
assumption.
clear IHt2.
assert (Is_true (balanced (insert x t1))).
apply IHt1.
unfold balanced in pre; intuition.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H0; intuition.
eauto.
rewrite t1b in H0.
unfold balanced in H0.
fold balanced in H0.
eapply S_NR_isBalancedSize.
apply andb_prop_elim in H0; intuition.
apply andb_prop_elim in H1; intuition.
apply andb_prop_elim in H0; intuition.
unfold balancedQ.
intuition.
assert (Is_true (isBalanced t2 (Bin s0 k1 eT Tip))).
eapply S_NRisBalanced.
clear H3.
assert (validsize_rec (insert x t1)).
apply validsize_insert.
eauto.
rewrite t1b in H2.
unfold size.
fold size.
assert (validsize (Bin s0 k1 eT Tip)).
eauto.
unfold validsize in H3.
unfold size in H3.
unfold realsize in H3.
fold realsize in H3.
rewrite <- H3.
clear H3.
assert (validsize eT).
eauto.
unfold validsize in H3.
rewrite H3.
clear - H1.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr in *.
psatzl Q.
rewrite unbalance in H2.
clear - H2.
generalize H2.
intuition.
(**** next, no rotation *)
rewrite <- t1b.
unfold balanceR.
assert (Is_true (isBalanced t2 (insert x t1))).
eapply S_NRisBalanced.
unfold isBalancedSize.
rewrite sizeT1.
clear - pre.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H; intuition.
apply andb_prop_elim in H1; intuition.
eapply S_NRisBalanced in H.
unfold isBalancedSize in H.
clear H.
eapply S_NRisBalanced in H3.
unfold isBalancedSize in H3.
assumption.
case_eq (isBalanced t2 (insert x t1)).
Focus 2.
intro f.
rewrite f in H.
apply False_ind.
generalize H.
intuition.
Unfocus.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H1; intuition.
assert (Is_true (balanced (insert x t2))).
apply H3.
eauto.
clear H3.
assert (Is_true (balanced (insert x t1))).
apply H1.
eauto.
clear H1.
apply andb_prop_elim in H4; intuition.
clear t1b eT s0 k1.
unfold bin.
unfold balanced.
fold balanced.
repeat (apply andb_prop_intro; intuition).
clear - sizeT1 H1.
eapply S_NRisBalanced.
eapply S_NRisBalanced in H1.
unfold isBalancedSize in *.
rewrite sizeT1.
assumption.
(* shallow case ended *)
(* deep case begins *)
intros s1 k2 dT cT.
intro cdb.
fold insert in IHt1.
fold insert in IHt2.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H; intuition.
apply andb_prop_elim in H2; intuition.
assert (Is_true (balanced (insert x t1))).
apply H.
eauto.
clear H.
assert (Is_true (balanced (insert x t2))).
apply H1.
eauto.
clear H1.
rewrite t1b in H2.
unfold balanced in H2.
fold balanced in H2.
apply andb_prop_elim in H2; intuition.
apply andb_prop_elim in H1; intuition.
apply andb_prop_elim in H2; intuition.
rewrite cdb in H6.
unfold balanced in H6.
fold balanced in H6.
apply andb_prop_elim in H6; intuition.
apply andb_prop_elim in H2; intuition.
apply andb_prop_elim in H6; intuition.
unfold balanceR.
case_eq (isBalanced t2 (Bin s0 k1 eT (Bin s1 k2 dT cT))).
intro bal.
unfold bin.
repeat (apply andb_prop_intro; intuition).
Focus 2.
rewrite <- cdb.
assumption.
Unfocus.
Focus 2.
rewrite <- cdb.
assumption.
Unfocus.
rewrite <- cdb.
rewrite <- t1b.
generalize size_insert.
intro si.
destruct si with x t1.
clear si.
eauto.
eapply S_NRisBalanced.
unfold isBalancedSize.
rewrite H6.
clear - H4 gp.
eapply S_NRisBalanced in H4.
unfold isBalancedSize in H4.
unfold good_params in gp.
unfold normal in gp.
psatzl Q.
eapply S_NRisBalanced.
unfold isBalancedSize.
rewrite H6.
clear - H4.
eapply S_NRisBalanced in H4.
unfold isBalancedSize in H4.
assumption.
intro unbalance.
generalize NR_deep_insert.
intuition.
generalize (H12 (size t2) (size t1) (size cT) (size dT) (size eT)).
clear H12.
intro dep.
compute [deep_insert balancedQ singly_balanced doubly_balanced] in dep.
(* size information will be used later *)
generalize (size_insert x t1).
intro sinsert.
Open Scope Q_scope.
assert (size (insert x t1) # 1 == 1 + (size t1 # 1)).
assert (validsize_rec t1).
eauto.
apply sinsert in H6.
clear sinsert.
destruct H6.
assumption.
apply False_ind.
clear dep.
rewrite t1b in H6.
rewrite cdb in H6.
assert (Is_true (isBalanced t2 (Bin s0 k1 eT (Bin s1 k2 dT cT)))).
eapply S_NRisBalanced.
unfold isBalancedSize.
rewrite H6.
eapply S_NRisBalanced in H4.
unfold isBalancedSize in H4.
clear H4.
eapply S_NRisBalanced in H5.
unfold isBalancedSize in H5.
assumption.
rewrite unbalance in H12.
clear - H12.
generalize H12.
intuition.
(* we have size information. *)
clear sinsert.
assert (validsize_rec (insert x t1)).
apply validsize_insert.
eauto.
rewrite t1b in *.
clear t1b.
rewrite cdb in *.
clear cdb.
assert (validsize_rec (Bin s1 k2 dT cT)) as sss.
eauto.
apply size_size_size in sss.
(* preparation done? *)
unfold rotateR.
unfold isSingle.
rewrite NR_SisSingleSize.
replace
  (isSingleSize (size (Bin s1 k2 dT cT) # 1) (size eT # 1))
  with
    (isSingleSize ((size cT # 1) + (size dT # 1) + 1) (size eT # 1)).
intuition.
assert (0 <= size t2 # 1).
apply (size_nneg).
eauto.
apply H13 in H14.
clear H13.
case_eq
(isSingleSize ((size cT # 1) + (size dT # 1) + 1) (size eT # 1)).
intro single.
rename H14 into H13.
rewrite single in H13.
intuition.
unfold singleR.
unfold bin.
unfold balanced.
fold balanced.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
rename H12 into vreco.
clear - H25 vreco sss.
(*** we can certainly make this part as a lemma and eauto it ***)
unfold isBalancedSize in *.
apply Qle_trans with
  ((size t2 # 1) + (size cT # 1) + (size dT # 1) + 1 + 1 + 1).
unfold size.
fold size.
Close Scope Q_scope.
replace s1 with (size dT + size cT + 1).
repeat rewrite bunsi_distr.
psatzl Q.
clear - sss.
psatzl Z.
assumption.
(* one goal now, this is much shorter *)
eapply S_NRisBalanced.
clear - H22 sss.
rewrite <- sss.
unfold isBalancedSize in *.
unfold size.
fold size.
repeat rewrite bunsi_distr in *.
psatzl Q.
(* another goal done *)
eapply S_NRisBalanced.
clear - H21 sss.
unfold size.
fold size.
rewrite <- sss.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr in *.
unfold Size in *.
psatzl Q.
eapply S_NRisBalanced.
clear - H17 sss.
rewrite <- sss.
unfold isBalancedSize in *.
unfold size.
fold size.
repeat rewrite bunsi_distr.
psatzl Q.
(* single rotation ended *)
intro double.
rewrite double in H14.
intuition.
assert (s1 = 1 + size dT + size cT).
assert (validsize (Bin s1 k2 dT cT)).
eauto.
unfold validsize in H23.
unfold realsize in H23.
unfold size in H23.
fold realsize in H23.
replace (size dT) with (realsize dT).
replace (size cT) with (realsize cT).
rewrite H23.
trivial.
assert (validsize cT).
eauto.
unfold validsize; trivial.
assert (validsize dT); eauto.
assert (s0 = 1 + size eT + s1).
assert (validsize (Bin s0 k1 eT (Bin s1 k2 dT cT))).
eauto.
unfold validsize in H26.
unfold realsize in H26.
fold realsize in H26.
unfold size in H26.
rewrite <- H26.
rewrite H23.
clear H26.
replace (realsize eT) with (size eT).
replace (realsize dT) with (size dT).
replace (realsize cT) with (size cT).
reflexivity.
assert (validsize cT); eauto.
assert (validsize dT); eauto.
assert (validsize eT); eauto.
rewrite H26 in *.
clear H26.
rewrite H23 in *.
clear H23.
unfold doubleR.
unfold bin.
unfold balanced.
fold balanced.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
unfold isBalancedSize.
unfold size.
fold size.
repeat rewrite bunsi_distr.
unfold isBalancedSize in H25.
clear - H25.
psatzl Q.
eapply S_NRisBalanced.
clear - H22.
unfold isBalancedSize in *.
unfold size.
fold size.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
intuition.
apply size_nneg.
eauto.
eapply S_NRisBalanced in H4.
eapply S_NRisBalanced in H5.
assumption.
eapply S_NRisBalanced in H4.
assumption.
clear H14.
clear H13.
intuition.
assert (Is_true
  (isBalanced t2 (Bin s0 k1 eT (Bin s1 k2 dT cT)))).
eapply S_NRisBalanced.
unfold size.
fold size.
unfold size in H6.
fold size in H6.
unfold isBalancedSize.
rewrite H6.
unfold isBalancedSize in H15.
clear - H15; psatzl Q.
rewrite unbalance in H16.
generalize H16.
intuition.
clear H14.
clear H13.
unfold size in H6.
fold size in H6.
assert (validsize (Bin s0 k1 eT (Bin s1 k2 dT cT))).
eauto.
unfold validsize in H13.
unfold realsize in H13.
fold realsize in H13.
unfold size in H13.
fold size in H13.
rewrite <- H13 in H6.
clear H13.
Open Scope Q_scope.
assert ((size t1 # 1) + 1 == 1 + (size t1 # 1)).
psatzl Q.
rewrite H13.
clear H13.
rewrite <- H6.
clear H6.
repeat rewrite bunsi_distr.
replace (size cT) with (realsize cT).
replace (size dT) with (realsize dT).
replace (size eT) with (realsize eT).
psatzl Q.
assert (validsize eT); eauto.
assert (validsize dT); eauto.
assert (validsize cT); eauto.
intuition.
apply size_nneg.
eauto.
apply size_nneg.
eauto.
clear H13.
eapply S_NRisBalanced; auto.
eapply S_NRisBalanced; auto.
intuition.
apply Qle_trans with (0 + 0 + 0).
intuition.
apply Qplus_le_compat.
apply Qplus_le_compat.
apply size_nneg.
eauto.
apply size_nneg; eauto.
intuition.
apply size_nneg; eauto.
clear H13.
eapply S_NRisBalanced in H8.
unfold size in H8.
fold size in H8.
rewrite <- sss in H8.
clear - H8.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr in H8.
psatzl Q.
clear H13.
eapply S_NRisBalanced in H1.
rewrite <-sss in H1.
clear - H1.
unfold size in H1.
fold size in H1.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr in H1.
psatzl Q.
clear dep.
rewrite <- sss.
unfold size.
fold size.
unfold isSingleSize.
  unfold Qlt_le_dec_bool.
case (
  Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
         (ratio * (1 + (size eT # 1)))).
case (
  Qlt_le_dec (1 + (1 + size dT + size cT # 1))
         (ratio * (1 + (size eT # 1)))).
auto.
intros.
apply False_ind.
clear - q q0.
generalize dependent (ratio * (1 + (size eT # 1))).
intros.
repeat rewrite bunsi_distr in q0.
psatzl Q.
case (Qlt_le_dec (1 + (1 + size dT + size cT # 1))
         (ratio * (1 + (size eT # 1)))).
clear.
intros.
repeat rewrite bunsi_distr in q.
psatzl Q.
auto.
fold insert in IHt2.
fold insert in IHt1.
intro eq.
clear eq.
unfold bin.
unfold balanced.
fold balanced.
unfold balanced in pre.
fold balanced in pre.
assumption.
intro lt.
clear lt.
fold insert.
fold insert in IHt2.
fold insert in IHt1.
unfold balanced in pre.
fold balanced in pre.
apply andb_prop_elim in pre; intuition.
apply andb_prop_elim in H; intuition.
apply andb_prop_elim in H2; intuition.
assert (Is_true (balanced (insert x t1))).
apply H.
eauto.
clear H.
assert (Is_true (balanced (insert x t2))).
apply H1.
eauto.
clear H1.
clear H2.
generalize size_insert.
intro si.
elim si with x t2.
clear si.
intro size_incr.
Focus 3.
eauto.
Unfocus.
Focus 2.
clear si.
intro unchange.
unfold balanceL.
assert (Is_true (isBalanced t1 (insert x t2))).
eapply S_NRisBalanced in H4.
eapply S_NRisBalanced.
unfold isBalancedSize in *.
rewrite unchange.
assumption.
case_eq (isBalanced t1 (insert x t2)).
intro bal.
unfold bin.
unfold balanced.
fold balanced.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
eapply S_NRisBalanced in H5.
unfold isBalancedSize in *.
rewrite unchange.
assumption.
intro f.
apply False_ind.
rewrite f in H1.
generalize H1; clear.
intuition.
Unfocus.
case_eq (insert x t2).
intro tip.
apply False_ind.
eapply insert_result_non_tip.
apply tip.
intros s0 k1 cdT eT.
intro t2b.
assert (validsize_rec (insert x t2)).
apply validsize_insert.
eauto.
rewrite t2b in H1.
assert (validsize (Bin s0 k1 cdT eT)).
eauto.
unfold validsize in H2.
unfold size in H2.
unfold realsize in H2.
fold realsize in H2.
replace (realsize cdT) with (size cdT) in H2.
replace (realsize eT) with (size eT) in H2.
rewrite <- H2 in *.
clear H2 s0.
case_eq cdT.
intro cdTtip.
rewrite cdTtip in *.
clear cdTtip.
unfold balanceL.
case_eq (
  isBalanced t1 (Bin (1 + size Tip + size eT)%Z k1 Tip eT)).
intro bal.
unfold bin.
unfold balanced.
fold balanced.
rewrite t2b in H.
unfold balanced in H.
fold balanced in H.
apply andb_prop_elim in H; intuition.
apply andb_prop_elim in H2; intuition.
apply andb_prop_elim in H; intuition.
clear H7.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
unfold size.
fold size.
eapply S_NRisBalanced in H5.
unfold isBalancedSize in *.
apply Qle_trans with
  (delta * (1 + (size t2 # 1))).
clear - H5.
psatzl Q.
rewrite <- size_incr.
rewrite t2b.
unfold size.
fold size.
apply Qmult_le_compat_l.
psatzl Q.
generalize gp; clear.
unfold good_params.
unfold normal.
psatzl Q.
intro unbalance.
generalize NR_shallow_insert.
intro si.
intuition.
rename H2 into si.
elim si with (size t1) (size eT).
clear si.
intro single.
intro si.
unfold shallow_singly_balanced in si.
unfold balancedQ in si.
intuition.
unfold rotateL.
assert (Is_true (isSingle Tip eT)).
unfold isSingle.
unfold size.
fold size.
clear - single.
rewrite NR_SisSingleSize.
assumption.
case_eq (isSingle Tip eT).
Focus 2.
intro double.
rewrite double in H11.
apply False_ind.
generalize H11; clear.
intuition.
Unfocus.
clear single.
intro single.
clear single.
clear H11.
unfold singleL.
unfold bin.
unfold balanced.
fold balanced.
rewrite t2b in *.
unfold balanced in H.
fold balanced in H.
apply andb_prop_elim in H; intuition.
apply andb_prop_elim in H11; intuition.
apply andb_prop_elim in H; intuition.
clear H15.
clear H7 H2 H6 H8.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
unfold size.
fold size.
clear - gp H10.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced.
clear - H13 gp.
unfold isBalancedSize in *.
unfold size; fold size.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
unfold balancedQ.
clear si.
assert (size eT = size t2).
rewrite t2b in size_incr.
unfold size in size_incr.
fold size in size_incr.
clear - size_incr.
generalize size_incr.
clear size_incr.
compute - [Zmult Zle Zlt Zplus size].
psatzl Z.
clear size_incr.
intuition.
apply size_nneg.
eauto.
apply size_nneg.
eauto.
unfold isBalancedSize.
rewrite H2.
eapply S_NRisBalanced in H4.
unfold isBalancedSize in H4.
assumption.
eapply S_NRisBalanced in H5.
unfold isBalancedSize in *.
rewrite H2.
assumption.
unfold balancedQ.
rewrite t2b in H.
unfold balanced in H.
fold balanced in H.
repeat (apply andb_prop_elim in H; destruct H).
intuition.
apply size_nneg.
eauto.
eapply S_NRisBalanced in H.
unfold size in H.
fold size in H.
assumption.
eapply S_NRisBalanced in H7.
unfold size in H7; fold size in H7.
assumption.
unfold balancedQ.
intuition.
assert (Is_true (isBalanced t1 (Bin (1 + size Tip + size eT)%Z k1 Tip eT))).
eapply S_NRisBalanced.
unfold size.
fold size.
clear - H7.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr.
psatzl Q.
rewrite unbalance in H8.
generalize H8; clear.
intuition.
intros s0 k2 cT dT.
intro cdb.
rewrite cdb in *.
clear cdb cdT.
Close Scope Q_scope.
assert (s0 = 1 + size cT + size dT).
assert (validsize (Bin s0 k2 cT dT)).
eauto.
unfold validsize in H2.
unfold realsize in H2.
fold realsize in H2.
unfold size in H2.
replace (size cT) with (realsize cT).
replace (size dT) with (realsize dT).
rewrite H2.
reflexivity.
assert (validsize dT); eauto.
assert (validsize cT); eauto.
rewrite H2 in *.
clear H2 s0.
rewrite t2b in *.
unfold balanced in H.
fold balanced in H.
repeat (apply andb_prop_elim in H; destruct H).
repeat (apply andb_prop_elim in H6; destruct H6).
unfold size in size_incr; fold size in size_incr.
repeat rewrite bunsi_distr in size_incr.
unfold balanceL.
case_eq (
  isBalanced t1
              (Bin
                 (1 + size (Bin (1 + size cT + size dT) k2 cT dT) + size eT)
                 k1 (Bin (1 + size cT + size dT) k2 cT dT) eT)
).
intro bal.
unfold bin.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
eapply S_NRisBalanced in H5.
unfold isBalancedSize in *.
unfold size; fold size.
repeat rewrite bunsi_distr.
rewrite size_incr.
clear size_incr.
unfold good_params in gp.
unfold normal in gp.
psatzl Q.
intro unbalance.
generalize (NR_deep_insert gp (size t1) (size t2) (size cT) (size dT) (size eT)).
intro dep.
compute [deep_insert balancedQ singly_balanced doubly_balanced] in dep.
unfold rotateL.
unfold isSingle.
rewrite NR_SisSingleSize.
replace (
  isSingleSize (size (Bin (1 + size cT + size dT) k2 cT dT) # 1)
              (size eT # 1)) with
  (isSingleSize
    ((size cT # 1) + (size dT # 1) + 1) (size eT # 1)).
intuition.
Open Scope Q_scope.
assert (0 <= size t1 # 1).
apply size_nneg.
eauto.
apply H11 in H12.
clear H11.
case_eq
(isSingleSize ((size cT # 1) + (size dT # 1) + 1) (size eT # 1)).
intro single.
rename H12 into H13.
rewrite single in H13.
intuition.
clear H13 H12 H14 H11 H16 H17.
unfold singleL.
unfold bin.
unfold balanced.
fold balanced.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
unfold isBalancedSize.
unfold isBalancedSize in H20.
unfold size; fold size.
repeat rewrite bunsi_distr.
clear - H20 gp.
unfold good_params in gp.
unfold normal in gp.
psatzl Q.
eapply S_NRisBalanced.
unfold size; fold size.
clear - H23.
unfold isBalancedSize in *.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced.
clear - H15.
unfold isBalancedSize in *.
unfold size; fold size.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced.
clear - H19.
unfold isBalancedSize in *.
unfold size; fold size.
repeat rewrite bunsi_distr.
psatzl Q.
intro double.
rewrite double in H12.
intuition.
unfold doubleL.
unfold bin.
unfold size; fold size.
unfold balanced; fold balanced.
clear H16 H17 H14 H13 H11.
clear H12.
repeat (apply andb_prop_intro; intuition).
eapply S_NRisBalanced.
clear - H20.
unfold isBalancedSize in *.
unfold size; fold size.
repeat rewrite bunsi_distr.
psatzl Q.
clear - H23.
eapply S_NRisBalanced.
unfold isBalancedSize in *.
unfold size; fold size.
repeat rewrite bunsi_distr.
psatzl Q.
eapply S_NRisBalanced; auto.
eapply S_NRisBalanced; auto.
eapply S_NRisBalanced; auto.
eapply S_NRisBalanced; auto.
clear H12.
clear H11.
intuition.
apply size_nneg.
eauto.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
intuition.
clear H11.
clear H12 H13 H14.
assert (
  Is_true
  (isBalanced t1
                (Bin
                   (1 + size (Bin (1 + size cT + size dT) k2 cT dT) + size eT)%Z
                   k1 (Bin (1 + size cT + size dT)%Z k2 cT dT) eT))).
eapply S_NRisBalanced.
unfold size; fold size.
unfold isBalancedSize.
repeat rewrite bunsi_distr.
rewrite size_incr.
unfold isBalancedSize in H15.
clear - H15; psatzl Q.
rewrite unbalance in H11.
generalize H11; clear; intuition.
clear H12.
clear H11.
clear unbalance.
clear - size_incr.
psatzl Q.
clear H12.
clear H11.
clear unbalance.
intuition.
apply size_nneg.
eauto.
apply size_nneg.
eauto.
eapply S_NRisBalanced.
assumption.
eapply S_NRisBalanced.
assumption.
clear H11 H12.
intuition.
apply Qle_trans with (0 + 0 + 0).
intuition.
repeat apply Qplus_le_compat.
apply size_nneg.
eauto.
apply size_nneg.
eauto.
intuition.
apply size_nneg.
eauto.
eapply S_NRisBalanced in H.
clear - H.
unfold isBalancedSize in *.
unfold size in H.
fold size in H.
repeat rewrite bunsi_distr in *.
psatzl Q.
clear - H7.
eapply S_NRisBalanced in H7.
unfold isBalancedSize in *.
generalize H7.
clear H7.
unfold size; fold size.
repeat rewrite bunsi_distr.
psatzl Q.
clear dep.
clear size_incr t2b unbalance.
unfold isSingleSize.
unfold Qlt_le_dec_bool.
unfold size; fold size.
case (Qlt_le_dec (1 + (1 + size cT + size dT # 1))).
case (Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
         (ratio * (1 + (size eT # 1)))).
auto.
intros.
apply False_ind.
clear - q q0.
repeat rewrite bunsi_distr in *.
generalize dependent (ratio * (1 + (size eT # 1))).
intro q.
psatzl Q.
case (Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
         (ratio * (1 + (size eT # 1)))).
clear.
intros.
apply False_ind.
generalize dependent (ratio * (1 + (size eT # 1))).
intro q.
repeat rewrite bunsi_distr in *.
psatzl Q.
auto.
assert (validsize eT); eauto.
assert (validsize cdT); eauto.
Qed.

Definition balance_rec (t: FSet) :=
  Is_true (balanced t).

(* this is the first one of the program lemmas *)

Lemma insert_balance:
    good_params ->
    forall (t: FSet) (k: K),
    balance_rec t -> validsize_rec t -> balance_rec (insert k t).
  intro gp.
  intros t k.
  apply insert_balanced.
  assumption.
  Qed.

Fixpoint deleteFindMin (t:FSet): (option K) * FSet :=
    (match t with
       | Bin _ kx Tip r => (Some kx,r)
       | Bin _ kx l r   =>
         match deleteFindMin l with
           (km,l') => (km, balanceL kx l' r)
         end
       | Tip => (None, Tip)
     end).

Fixpoint deleteFindMax (t:FSet): (option K) * FSet :=
  match t with
    | Bin _ kx l Tip => ((Some kx),l)
    | Bin _ kx l r   =>
      match deleteFindMax r with
        (km,r') => (km,balanceR kx l r')
      end
    |  Tip            => (None, Tip)
  end.


Close Scope Q_scope.

Lemma sizepos_bin:
  forall (t: FSet),
    size t > 0 -> t <> Tip.
  intro t.
  intro pos.
  destruct t.
  apply False_ind.
  generalize pos.
  unfold size.
  intuition.
  discriminate.
  Qed.

Lemma bin_delFM_decr:
  forall (t: FSet),
    t <> Tip -> validsize_rec t ->
    exists t': FSet,
      exists x: K,
        deleteFindMin t = (Some x, t') /\
        size t' + 1 = size t /\
        validsize_rec t'.
  intro t.
  intro nontip.
  induction t.
  apply False_ind.
  generalize nontip.
  intuition.
  clear nontip.
  unfold deleteFindMin.
  fold deleteFindMin.
  intro vrec.
  destruct t1.
  destruct t2.
  clear IHt1.
  clear IHt2.
  exists Tip.
  exists k.
  split.
  reflexivity.
  unfold size.
  assert (validsize (Bin s k Tip Tip)).
  eauto.
  unfold validsize in H.
  unfold realsize in H.
  unfold size in H.
  split.
  psatzl Z.
  compute.
  reflexivity.
  clear IHt1.
  exists (Bin s0 k0 t2_1 t2_2).
  exists k.
  split.
  reflexivity.
  unfold size.
  assert (validsize (Bin s k Tip (Bin s0 k0 t2_1 t2_2))).
  eauto.
  split.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  unfold realsize.
  clear H.
  fold realsize.
  assert (validsize ((Bin s0 k0 t2_1 t2_2))).
  eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  unfold realsize.
  fold realsize.
  psatzl Z.
  eauto.
  assert (
         exists t' : FSet,
           exists x : K,
             deleteFindMin (Bin s0 k0 t1_1 t1_2) = (Some x, t') /\
             size t' + 1 = size (Bin s0 k0 t1_1 t1_2) /\ validsize_rec t'
  ).
  apply IHt1.
  discriminate.
  eauto.
  destruct H.
  destruct H.
  exists (balanceL k x t2).
  exists x0.
  split.
  destruct H.
  rewrite H.
  reflexivity.
  destruct H.
  generalize (size_balanceL k x t2).
  intro sb.
  split.
  assert (validsize_rec x).
  intuition.
  apply sb in H1.
  clear sb.
  unfold size.
  fold size.
  assert (validsize (Bin s k (Bin s0 k0 t1_1 t1_2) t2)).
  eauto.
  unfold validsize in H2.
  unfold realsize in H2.
  fold realsize in H2.
  unfold size in H2.
  rewrite <- H2.
  clear H2.
  unfold size in H0.
  fold size in H0.
  assert (validsize (Bin s0 k0 t1_1 t1_2)).
  eauto.
  unfold validsize in H2.
  unfold realsize in H2.
  fold realsize in H2.
  unfold size in H2.
  rewrite H2.
  clear H2.
  destruct H0.
  rewrite <- H0.
  clear H0.
  replace (realsize t2) with (size t2).
  generalize H1; clear.
  compute -[Zmult Zplus Zle Zlt balanceL size].
  psatzl Z.
  assert (validsize t2); eauto.
  eauto.
  apply validsize_balanceL.
  intuition.
  eauto.
  Qed.

Lemma balanceL_balance:
  forall (x: K) (l r:FSet),
    good_params ->
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    Is_true (isBalancedSizeZ (size l + 1) (size r)) ->
    Is_true (isBalancedSizeZ (size r) (size l + 1)) ->
    Is_true (balanced (balanceL x l r)).
  intros.
  unfold balanceL.
  case_eq (isBalanced l r).
  intro bal.
  unfold bin.
  unfold balanced; fold balanced.
  repeat (apply andb_prop_intro; intuition).
  clear - H5 H H0 H1.
  rewrite S_NR_isBalancedSize in H5.
  eapply S_NRisBalanced.
  unfold isBalancedSize in *.
  unfold good_params in *.
  unfold normal in *.
  rewrite bunsi_distr in H5.
  psatzl Q.
  intro unbalance.
  unfold rotateL.
  destruct r.
  unfold assert_false.
  unfold bin.
  unfold balanced.
  fold balanced.
  apply False_ind.
  assert (Is_true (isBalanced l Tip)).
  eapply S_NRisBalanced.
  unfold isBalancedSize.
  unfold size.
  fold size.
  Open Scope Q_scope.
  apply Qle_trans with (delta * (0 + 1)).
  unfold good_params in *.
  unfold normal in *.
  psatzl Q.
  apply Qmult_le_compat_l.
  apply Qplus_le_compat.
  apply size_nneg.
  eauto.
  intuition.
  unfold good_params in *.
  unfold normal in *.
  psatzl Q.
  rewrite unbalance in H6.
  generalize H6; clear; intuition.
  unfold balanced in H3.
  fold balanced in H3.
  rename H into gp.
  rename H3 into H.
  repeat (apply andb_prop_elim in H; destruct H).
  assert (validsize (Bin s k r1 r2)).
  eauto.
  unfold validsize in H8.
  unfold realsize in H8.
  fold realsize in H8.
  unfold size in H8.
  replace (realsize r1) with (size r1) in H8.
  replace (realsize r2) with (size r2) in H8.
  rewrite <- H8 in *.
  clear H8.
  destruct r1.
  (* this is the shallow case *)
  generalize (NR_shallow_delete gp (size l) (size r2)).
  intro sd.
  unfold shallow_delete in sd.
  unfold shallow_singly_balanced in sd.
  unfold balancedQ in sd.
  intuition.
  assert (0 <= size l # 1).
  apply size_nneg.
  eauto.
  apply sd in H8.
  clear sd.
  intuition.
  clear H11 H12 H10 H8.
  assert (Is_true (isSingle Tip r2)).
  unfold isSingle.
  rewrite NR_SisSingleSize.
  unfold size; fold size.
  assumption.
  case_eq (isSingle Tip r2).
  intro single.
  clear single.
  unfold singleL.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  repeat (apply andb_prop_intro; intuition).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H14; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H17; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  assumption.
  eapply S_NRisBalanced.
  unfold size; fold size; auto.
  intro double.
  rewrite double in H8.
  apply False_ind.
  generalize H8; clear.
  intuition.
  clear H8.
  clear sd.
  intuition.
  assert (0 <= (size l # 1)).
  apply size_nneg.
  eauto.
  psatzl Q.
  assert (0 <= (size r2 # 1)).
  apply size_nneg.
  eauto.
  psatzl Q.
  eapply S_NR_isBalancedSize in H4.
  unfold size in H4.
  fold size in H4.
  generalize H4.
  clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NR_isBalancedSize in H5.
  generalize H5.
  clear.
  unfold isBalancedSize.
  unfold size; fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  intuition.
  clear H10.
  clear H8.
  apply size_nneg.
  eauto.
  clear H10.
  clear H8.
  clear unbalance.
  clear H5.
  clear H4.
  eapply S_NRisBalanced in H.
  generalize H.
  clear.
  unfold isBalancedSize.
  unfold size; fold size.
  auto.
  clear H10.
  clear H8.
  clear unbalance.
  clear H5.
  eapply S_NRisBalanced in H7.
  unfold size in H7.
  fold size in H7.
  assumption.
  intuition.
  clear H14.
  assert (Is_true
    (isBalanced l (Bin (1 + size Tip + size r2)%Z k Tip r2))).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H11; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  rewrite unbalance in H12.
  generalize H12; compute.
  auto.
  (*** this is the double case ***)
  unfold balanced in H6.
  fold balanced in H6.
  rename H into H8.
  repeat (apply andb_prop_elim in H; destruct H).
  assert (validsize (Bin s0 k0 r1_1 r1_2)).
  eauto.
  unfold validsize in H.
  unfold realsize in H.
  fold realsize in H.
  unfold size in H.
  replace (realsize r1_1) with (size r1_1) in H.
  replace (realsize r1_2) with (size r1_2) in H.
  rename r1_1 into cT.
  rename r1_2 into dT.
  rewrite <- H in *.
  clear H.
  apply andb_prop_elim in H6.
  destruct H6.
  apply andb_prop_elim in H; destruct H.
  apply andb_prop_elim in H; destruct H.
  rename l into aT.
  unfold size in *.
  fold size.
  fold size in unbalance.
  fold size in H5.
  fold size in H4.
  fold size in H8.
  fold size in H1.
  fold size in H7.
  rename r2 into eT.
  generalize (NR_deep_delete gp (size aT) (1 + (1 + size cT + size dT) + size eT)
    (size cT) (size dT) (size eT)).
  intro dd.
  unfold deep_delete in dd.
  assert (0 <= size aT # 1).
  apply size_nneg.
  eauto.
  apply dd in H11.
  clear dd.
  case_eq (isSingleSize ((size cT # 1) + (size dT # 1) + 1) (size eT # 1)).
  intro single.
  rewrite single in H11.
  case_eq (isSingle (Bin (1 + size cT + size dT)%Z k0 cT dT) eT).
  intro single2.
  clear single.
  clear single2.
  Focus 2.
  intro f.
  unfold isSingle in f.
  rewrite NR_SisSingleSize in f.
  clear - single f.
  apply False_ind.
  generalize single f.
  clear.
  unfold isSingleSize in *.
  unfold Qlt_le_dec_bool in *.
  case (Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
                 (ratio * (1 + (size eT # 1)))).
  intro lt.
  case (Qlt_le_dec
            (1 + (size (Bin (1 + size cT + size dT)%Z k0 cT dT) # 1))
            (ratio * (1 + (size eT # 1)))).
  intuition.
  intuition.
  clear single f.
  unfold size in q.
  fold size in q.
  repeat rewrite bunsi_distr in q.
  generalize dependent (ratio * (1 + (size eT # 1))).
  intro q.
  psatzl Q.
  intuition.
  Unfocus.
  unfold singly_balanced in H11.
  unfold balancedQ in H11.
  intuition.
  clear H11 H13 H14 H12.
  clear H16 H17.
  unfold singleL.
  unfold bin.
  unfold size; fold size.
  unfold balanced.
  fold balanced.
  repeat (apply andb_prop_intro; intuition).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H20 ; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H23; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  generalize H15 ; clear.
  unfold isBalancedSize.
  unfold size; fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H19; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  intro double.
  case_eq (isSingle (Bin (1 + size cT + size dT)%Z k0 cT dT) eT).
  intro single.
  apply False_ind.
  unfold isSingle in single.
  rewrite NR_SisSingleSize in single.
  generalize double single.
  clear.
  unfold isSingleSize.
  unfold Qlt_le_dec_bool.
  case (Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
         (ratio * (1 + (size eT # 1)))).
  intuition.
  case (Qlt_le_dec (1 + (size (Bin (1 + size cT + size dT)%Z k0 cT dT) # 1))
         (ratio * (1 + (size eT # 1)))).
  generalize (ratio * (1 + (size eT # 1))).
  intro q.
  unfold size ;fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  intuition.
  intro double2.
  rewrite double in H11.
  clear double.
  unfold doubly_balanced in H11.
  unfold balancedQ in H11.
  intuition.
  clear H11 H13 H14 H12 H16 H17.
  unfold doubleL.
  unfold bin.
  unfold balanced; fold balanced.
  repeat (apply andb_prop_intro; intuition).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H20; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H23; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  assumption.
  eapply S_NRisBalanced; auto.
  eapply S_NRisBalanced; auto.
  eapply S_NRisBalanced; auto.
  unfold balancedQ.
  intuition.
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  intuition.
  apply size_nneg.
  eauto.
  repeat rewrite bunsi_distr.
  apply Qle_trans with (0 + (0 + 0 + 0) + 0).
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  intuition.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  clear H12; clear H11; clear unbalance.
  eapply S_NR_isBalancedSize in H4.
  generalize H4; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  clear H11 H12.
  clear unbalance.
  eapply S_NR_isBalancedSize in H5.
  generalize H5.
  clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  clear H11.
  clear dd.
  unfold balancedQ.
  intuition.
  clear H12.
  clear H11.
  eapply S_NR_isBalancedSize in H13.
  unfold isBalanced in unbalance.
  unfold size in unbalance.
  fold size in unbalance.
  eapply S_NR_isBalancedSize in H15.
  rewrite unbalance in H13.
  generalize H13; clear.
  intuition.
  clear dd H11.
  repeat rewrite bunsi_distr.
  psatzl Q.
  clear H11.
  clear dd.
  unfold balancedQ.
  intuition.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  eapply S_NR_isBalancedSize.
  assumption.
  eapply S_NR_isBalancedSize.
  assumption.
  unfold balancedQ.
  intuition.
  clear H12.
  clear H11.
  clear unbalance.
  apply Qle_trans with (0 + 0 + 0).
  intuition.
  repeat apply Qplus_le_compat.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  intuition.
  apply size_nneg.
  eauto.
  clear H11 H12.
  clear unbalance.
  clear H4 H5.
  eapply S_NR_isBalancedSize in H8.
  unfold size in H8.
  fold size in H8.
  generalize H8.
  clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  clear H11 H12.
  eapply S_NR_isBalancedSize in H7.
  generalize H7.
  clear.
  unfold isBalancedSize.
  unfold size; fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  assert (validsize r1_2); eauto.
  assert (validsize r1_1); eauto.
  assert (validsize r2) ; eauto.
  assert (validsize r1) ; eauto.
  Qed.
  
Lemma delFMin_balanced:
  forall (t: FSet),
    good_params ->
    Is_true (balanced t) ->
    validsize_rec t ->
    match (deleteFindMin t) with (m, t') =>
      Is_true (balanced t')
    end.
  intro t.
  intro gp.
  intro pre.
  intro vrec.
  induction t.
  unfold deleteFindMin.
  assumption.
  unfold balanced in pre.
  fold balanced in pre.
  rename pre into H.
  repeat (apply andb_prop_elim in H; destruct H).
  assert (let (_, t') := deleteFindMin t1 in Is_true (balanced t')).
  apply IHt1.
  assumption.
  eauto.
  clear IHt1.
  unfold deleteFindMin.
  clear IHt2.
  fold deleteFindMin.
  case_eq t1.
  intro tip.
  assumption.
  intros s0 k0 t1_1 t1_2.
  intro t1b.
  rewrite <- t1b.
  case_eq (deleteFindMin t1).
  intros o t'.
  intro t1del.
  rewrite t1del in H3.
  generalize (bin_delFM_decr t1).
  intro decr.
  assert (t1 <> Tip).
  rewrite t1b.
  discriminate.
  apply decr in H4.
  clear decr.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  assert (x = t').
  rewrite t1del in H4.
  replace x with (snd (Some x0, x)).
  replace t' with (snd (o, t')).
  rewrite H4.
  trivial.
  intuition.
  intuition.
  rewrite H7 in *.
  clear H7.
  replace o with (Some x0) in *.
  clear H4.
  apply balanceL_balance.
  assumption.
  eauto.
  eauto.
  assumption.
  assumption.
  rewrite H5.
  unfold isBalanced in H.
  assumption.
  rewrite H5.
  unfold isBalanced in H2.
  assumption.
  replace (Some x0) with (fst (Some x0, t')).
  replace o with (fst (o, t')).
  rewrite H4 in t1del.
  rewrite t1del.
  trivial.
  intuition.
  intuition.
  eauto.
  Qed.

Close Scope Q_scope.
  
Lemma balanceR_balance:
  forall (x: K) (l r: FSet),
    good_params ->
    validsize_rec r ->
    validsize_rec l ->
    Is_true (balanced r) ->
    Is_true (balanced l) ->
    Is_true (isBalancedSizeZ (size r + 1) (size l)) ->
    Is_true (isBalancedSizeZ (size l) (size r + 1)) ->
    Is_true (balanced (balanceR x l r)).
  intros.
  unfold balanceR.
  case_eq (isBalanced r l).
  intro bal.
  unfold bin.
  unfold balanced; fold balanced.
  repeat (apply andb_prop_intro;intuition).
  clear - H5 H H0 H1.
  rewrite S_NR_isBalancedSize in H5.
  eapply S_NRisBalanced.
  unfold isBalancedSize in *.
  unfold good_params in *.
  unfold normal in *.
  rewrite bunsi_distr in H5.
  psatzl Q.
  intro unbalance.
  unfold rotateR.
  destruct l.
  unfold assert_false.
  unfold bin.
  unfold balanced.
  fold balanced.
  apply False_ind.
  assert (Is_true (isBalanced r Tip)).
  eapply S_NRisBalanced.
  unfold isBalancedSize.
  unfold size.
  fold size.
  Open Scope Q_scope.
  apply Qle_trans with (delta * (0 + 1)).
  unfold good_params in *.
  unfold normal in *.
  psatzl Q.
  apply Qmult_le_compat_l.
  apply Qplus_le_compat.
  apply size_nneg.
  eauto.
  intuition.
  unfold good_params in *.
  unfold normal in *.
  psatzl Q.
  rewrite unbalance in H6.
  generalize H6 ;clear ; intuition.
  unfold balanced in H3.
  fold balanced in H3.
  rename H into gp.
  rename H3 into H.
  repeat (apply andb_prop_elim in H; destruct H).
  assert (validsize (Bin s k l1 l2)).
  eauto.
  unfold validsize in H8.
  unfold realsize in H8.
  fold realsize in H8.
  unfold size in H8.
  replace (realsize l1) with (size l1) in H8.
  replace (realsize l2) with (size l2) in H8.
  rewrite <- H8 in *.
  clear H8.
  destruct l2.
  generalize (NR_shallow_delete gp (size r) (size l1)).
  intro sd.
  unfold shallow_delete in sd.
  unfold shallow_singly_balanced in sd.
  unfold balancedQ in sd.
  intuition.
  assert (0<= size r #1).
  apply size_nneg.
  eauto.
  apply sd in H8.
  clear sd.
  intuition.
  clear H11 H12 H10 H8.
  assert (Is_true (isSingle Tip l1)).
  unfold isSingle.
  rewrite NR_SisSingleSize.
  unfold size; fold size.
  assumption.
  case_eq (isSingle Tip l1).
  intro single.
  clear single.
  unfold singleR.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  repeat (apply andb_prop_intro; intuition).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H17; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H14; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  assumption.
  eapply S_NRisBalanced.
  unfold size; fold size; auto.
  intro double.
  rewrite double in H8.
  apply False_ind.
  generalize H8; clear.
  intuition.
  clear H8.
  clear sd.
  intuition.
  assert (0 <= (size r # 1)).
  apply size_nneg.
  eauto.
  psatzl Q.
  assert (0 <= (size l1 # 1)).
  apply size_nneg.
  eauto.
  psatzl Q.
  eapply S_NR_isBalancedSize in H4.
  generalize H4.
  unfold size; fold size.
  clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NR_isBalancedSize in H5.
  generalize H5.
  clear.
  unfold isBalancedSize.
  unfold size; fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  intuition.
  apply size_nneg.
  eauto.
  clear H10 H8.
  eapply S_NRisBalanced in H7.
  generalize H7.
  unfold size; fold size.
  auto.
  clear H8 H10.
  eapply S_NRisBalanced in H.
  generalize H.
  unfold size; fold size.
  auto.
  intuition.
  clear H14.
  assert (Is_true
    (isBalanced r (Bin (1 + size l1 + size Tip)%Z k l1 Tip))).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H11; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  rewrite unbalance in H12.
  generalize H12; clear ;compute.
  auto.
  (*** this is the double case ***)
  rename H3 into tmp.
  rename H6 into H3.
  rename tmp into H6.
  unfold balanced in H6.
  fold balanced in H6.
  rename H into H8.
  rename H6 into H.
  repeat (apply andb_prop_intro in H; destruct H).
  assert (validsize (Bin s0 k0 l2_1 l2_2)).
  eauto.
  unfold validsize in H6.
  unfold realsize in H6.
  fold realsize in H6.
  unfold size in H6.
  replace (realsize l2_1) with (size l2_1) in H6.
  replace (realsize l2_2) with (size l2_2) in H6.
  rewrite <- H6 in *.
  clear H6.
  rename r into aT.
  unfold size in *.
  fold size.
  fold size in unbalance.
  fold size in H5.
  fold size in H4.
  fold size in H8.
  fold size in H1.
  fold size in H7.
  rename l1 into eT.
  rename l2_1 into dT.
  rename l2_2 into cT.
  generalize (NR_deep_delete gp (size aT) (1 + size eT + (1 + size dT + size cT))%Z
    (size cT) (size dT) (size eT)).
  intro dd.
  unfold deep_delete in dd.
  assert (0 <= size aT # 1).
  apply size_nneg.
  eauto.
  apply dd in H6.
  clear dd.
  case_eq (isSingleSize ((size cT # 1) + (size dT # 1) + 1) (size eT # 1)).
  intro single.
  rewrite single in H6.
  case_eq (isSingle (Bin (1 + size dT + size cT)%Z k0 dT cT) eT).
  intro single2.
  clear single.
  clear single2.
  Focus 2.
  intro f.
  unfold isSingle in f.
  rewrite NR_SisSingleSize in f.
  clear - single f.
  apply False_ind.
  generalize single f.
  clear.
  unfold isSingleSize in *.
  unfold Qlt_le_dec_bool in *.
  case (Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
         (ratio * (1 + (size eT # 1)))).
  intro lt.
  case (Qlt_le_dec (1 + (size (Bin (1 + size dT + size cT)%Z k0 dT cT) # 1))
         (ratio * (1 + (size eT # 1)))).
  intuition.
  intuition.
  clear single f.
  unfold size in q.
  fold size in q.
  repeat rewrite bunsi_distr in q.
  generalize dependent (ratio * (1 + (size eT # 1))).
  intro.
  psatzl Q.
  intuition.
  Unfocus.
  unfold singly_balanced in H6.
  unfold balancedQ in H6.
  rename H6 into H11.
  intuition.
  clear H10 H9 H11 H6.
  clear H13 H14.
  unfold singleR.
  unfold bin.
  unfold size; fold size.
  unfold balanced.
  fold balanced.
  repeat (apply andb_prop_intro; intuition).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H20 ; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H17; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  generalize H16 ; clear.
  unfold isBalancedSize.
  unfold size; fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H12; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  intro double.
  case_eq (isSingle (Bin (1 + size dT + size cT)%Z k0 dT cT) eT).
  intro single.
  apply False_ind.
  unfold isSingle in single.
  rewrite NR_SisSingleSize in single.
  generalize double single.
  clear.
  unfold isSingleSize.
  unfold Qlt_le_dec_bool.
  case (Qlt_le_dec (1 + ((size cT # 1) + (size dT # 1) + 1))
         (ratio * (1 + (size eT # 1)))).
  intuition.
  case (Qlt_le_dec (1 + (size (Bin (1 + size dT + size cT)%Z k0 dT cT) # 1))
         (ratio * (1 + (size eT # 1)))).
  generalize (ratio * (1 + (size eT # 1))).
  intro q.
  unfold size ;fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  intuition.
  intro double2.
  rewrite double in H6.
  clear double.
  unfold doubly_balanced in H6.
  unfold balancedQ in H6.
  intuition.
  clear H13 H9.
  clear H10 H11.
  clear H6 H14.
  unfold doubleR.
  unfold bin.
  unfold balanced; fold balanced.
  repeat (apply andb_prop_intro; intuition).
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H20; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  unfold size; fold size.
  generalize H17; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NRisBalanced.
  assumption.
  eapply S_NRisBalanced; auto.
  apply andb_prop_elim in H; intuition.
  apply andb_prop_elim in H6 ;intuition.
  apply andb_prop_elim in H; intuition.
  apply andb_prop_elim in H6; intuition.
  apply andb_prop_elim in H; intuition.
  eapply S_NRisBalanced; auto.
  eapply S_NRisBalanced; auto.
  apply andb_prop_elim in H; intuition.
  unfold balancedQ.
  intuition.
  apply Qle_trans with (0 + 0).
  intuition.
  apply Qplus_le_compat.
  intuition.
  apply size_nneg.
  eauto.
  repeat rewrite bunsi_distr.
  apply Qle_trans with (0 + 0 + (0 + 0 + 0)).
  intuition.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  intuition.
  apply size_nneg.
  eauto.
  apply Qplus_le_compat.
  apply Qplus_le_compat.
  intuition.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  clear H6 H9.
  eapply S_NR_isBalancedSize in H4.
  generalize H4; clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NR_isBalancedSize in H5.
  generalize H5.
  clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  clear H6.
  clear dd.
  unfold balancedQ.
  intuition.
  clear H9.
  clear H6.
  eapply S_NR_isBalancedSize in H10.
  unfold isBalanced in unbalance.
  unfold size in unbalance.
  fold size in unbalance.
  rewrite unbalance in H10.
  generalize H10; clear.
  intuition.
  clear dd H6.
  repeat rewrite bunsi_distr.
  psatzl Q.
  unfold balancedQ.
  intuition.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  eapply S_NR_isBalancedSize.
  clear H6.
  clear H9.
  apply andb_prop_elim in H; intuition.
  apply andb_prop_elim in H6;intuition.
  apply andb_prop_elim in H; intuition.
  eapply S_NR_isBalancedSize.
  apply andb_prop_elim in H;intuition.
  apply andb_prop_elim in H10; intuition.
  apply andb_prop_elim in H;intuition.
  unfold balancedQ.
  intuition.
  clear H6 H9.
  apply Qle_trans with (0 + 0 + 0).
  intuition.
  repeat apply Qplus_le_compat.
  apply size_nneg.
  eauto.
  apply size_nneg.
  eauto.
  intuition.
  apply size_nneg.
  eauto.
  clear H8.
  rename H7 into H8.
  eapply S_NR_isBalancedSize in H8.
  unfold size in H8.
  fold size in H8.
  generalize H8.
  clear.
  unfold isBalancedSize.
  repeat rewrite bunsi_distr.
  psatzl Q.
  eapply S_NR_isBalancedSize in H8.
  generalize H8.
  clear.
  unfold isBalancedSize.
  unfold size; fold size.
  repeat rewrite bunsi_distr.
  psatzl Q.
  assert (validsize l2_2); eauto.
  assert (validsize l2_1); eauto.
  assert (validsize l2) ; eauto.
  assert (validsize l1) ; eauto.
  Qed.

Close Scope Q_scope.
  
Lemma bin_delFMax_decr:
  forall (t: FSet),
    t <> Tip -> validsize_rec t ->
    exists t': FSet,
      exists x: K,
        deleteFindMax t = (Some x, t') /\
        size t' + 1 = size t /\
        validsize_rec t'.
  intro t.
  intro nontip.
  induction t.
  apply False_ind.
  generalize nontip.
  intuition.
  clear nontip.
  unfold deleteFindMax.
  fold deleteFindMax.
  intro vrec.
  destruct t2.
  destruct t1.
  clear IHt1.
  clear IHt2.
  exists Tip.
  exists k.
  split.
  reflexivity.
  unfold size.
  assert (validsize (Bin s k Tip Tip)).
  eauto.
  unfold validsize in H.
  unfold realsize in H.
  unfold size in H.
  split.
  psatzl Z.
  compute.
  reflexivity.
  clear IHt2.
  exists (Bin s0 k0 t1_1 t1_2).
  exists k.
  split.
  reflexivity.
  unfold size.
  assert (validsize (Bin s k (Bin s0 k0 t1_1 t1_2) Tip)).
  eauto.
  split.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  unfold realsize.
  clear H.
  fold realsize.
  assert (validsize (Bin s0 k0 t1_1 t1_2)).
  eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  unfold realsize.
  fold realsize.
  psatzl Z.
  eauto.
  assert (
         exists t' : FSet,
           exists x : K,
             deleteFindMax (Bin s0 k0 t2_1 t2_2) = (Some x, t') /\
             size t' + 1 = size (Bin s0 k0 t2_1 t2_2) /\ validsize_rec t'
  ).
  apply IHt2.
  discriminate.
  eauto.
  clear IHt1.
  clear IHt2.
  destruct H.
  destruct H.
  exists (balanceR k t1 x).
  exists x0.
  split.
  destruct H.
  rewrite H.
  reflexivity.
  destruct H.
  generalize (size_balanceR k t1 x).
  intro sb.
  split.
  assert (validsize_rec x).
  intuition.
  apply sb in H1.
  clear sb.
  unfold size.
  fold size.
  assert (validsize (Bin s k t1 (Bin s0 k0 t2_1 t2_2))).
  eauto.
  unfold validsize in H2.
  unfold realsize in H2.
  fold realsize in H2.
  unfold size in H2.
  rewrite <- H2.
  clear H2.
  unfold size in H0.
  fold size in H0.
  assert (validsize (Bin s0 k0 t2_1 t2_2)).
  eauto.
  unfold validsize in H2.
  unfold realsize in H2.
  fold realsize in H2.
  unfold size in H2.
  rewrite H2.
  clear H2.
  destruct H0.
  rewrite <- H0.
  clear H0.
  replace (realsize t1) with (size t1).
  generalize H1; clear.
  compute -[Zmult Zplus Zle Zlt balanceR size].
  psatzl Z.
  assert (validsize t1); eauto.
  eauto.
  apply validsize_balanceR.
  intuition.
  eauto.
intuition.
  Qed.


Lemma delFMax_balanced:
  forall (t: FSet),
    good_params ->
    Is_true (balanced t) ->
    validsize_rec t ->
    match (deleteFindMax t) with (m, t') =>
      Is_true (balanced t')
    end.
  intro t.
  intro gp.
  intro pre.
  intro vrec.
  induction t.
  unfold deleteFindMax.
  assumption.
  unfold balanced in pre.
  fold balanced in pre.
  rename pre into H.
  repeat (apply andb_prop_elim in H; destruct H).
  assert (let (_, t') := deleteFindMax t2 in Is_true (balanced t')).
  apply IHt2.
  assumption.
  eauto.
  clear IHt2.
  unfold deleteFindMax.
  clear IHt1.
  fold deleteFindMax.
  case_eq t2.
  intro tip.
  assumption.
  intros s0 k0 t2_1 t2_2.
  intro t2b.
  rewrite <- t2b.
  case_eq (deleteFindMax t2).
  intros o t'.
  intro t2del.
  rewrite t2del in H3.
  generalize (bin_delFMax_decr t2).
  intro decr.
  assert (t2 <> Tip).
  rewrite t2b.
  discriminate.
  apply decr in H4.
  clear decr.
  destruct H4.
  destruct H4.
  destruct H4.
  destruct H5.
  assert (x = t').
  rewrite t2del in H4.
  replace x with (snd (Some x0, x)).
  replace t' with (snd (o, t')).
  rewrite H4.
  trivial.
  intuition.
  intuition.
  rewrite H7 in *.
  clear H7.
  replace o with (Some x0) in *.
  clear H4.
  apply balanceR_balance.
  assumption.
  eauto.
  eauto.
  assumption.
  assumption.
  rewrite H5.
  unfold isBalanced in H.
  assumption.
  rewrite H5.
  unfold isBalanced in H2.
  assumption.
  replace (Some x0) with (fst (Some x0, t')).
  replace o with (fst (o, t')).
  rewrite H4 in t2del.
  rewrite t2del.
  trivial.
  intuition.
  intuition.
  eauto.
Qed.

Fixpoint glue (l r: FSet) :=
  match l with
    | Tip => r
    | _ =>
      match r with
        | Tip => l
        | _ => 
          if Zle_bool (size l) (size r) then
          match deleteFindMin r with
            | ((Some km),r') => balanceR km l r'
            | (None, _) => Tip
          end
          else
            match deleteFindMax l with
              | ((Some km),l') => balanceL km l' r
              | (None, _) => Tip
            end
      end
  end.

Lemma glue_decr:
  good_params ->
  forall (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    Is_true (isBalanced l r) ->
    Is_true (isBalanced r l) ->
    (size (glue l r) = (size l) + (size r)) /\
    validsize_rec (glue l r) /\
    Is_true (balanced (glue l r)).
  intro gp.
  intros l r.
  intros lvrec rvrec.
  intros lbal rbal.
  intros lrbal rlbal.
  split.
  unfold glue.
  destruct l.
  unfold size.
  fold size.
  generalize (size r).
  intro s.
  unfold Size in *.
  ring.
  destruct r.
  unfold size; fold size.
  unfold Size in s.
  clear.
  ring_simplify.
  reflexivity.
  case_eq (Zle_bool (size (Bin s k l1 l2)) (size (Bin s0 k0 r1 r2))).
  intro le.
  generalize (bin_delFM_decr (Bin s0 k0 r1 r2)).
  intro decr.
  assert (exists t' : FSet,
           exists x : K,
             deleteFindMin (Bin s0 k0 r1 r2) = (Some x, t') /\
             size t' + 1 = size (Bin s0 k0 r1 r2) /\ validsize_rec t').
  apply decr.
  discriminate.
  eauto.
  clear decr.
  rename H into decr.
  destruct decr.
  destruct H.
  destruct H.
  destruct H0.
  rewrite H.
  generalize (size_balanceR x0 (Bin s k l1 l2) x).
  intro sb.
  assert (       (size (balanceR x0 (Bin s k l1 l2) x) # 1 ==
        1 + (size (Bin s k l1 l2) # 1) + (size x # 1))%Q
).
  apply sb.
  eauto.
  eauto.
  clear sb.
  assert (
    (size (balanceR x0 (Bin s k l1 l2) x) =
        1 + (size (Bin s k l1 l2)) + (size x))).
  generalize H2.
  clear H2.
  compute -[Zmult Zle Zplus balanceR size Zlt].
  psatzl Z.
  clear H2.
  rewrite H3.
  rewrite <- H0.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.
  intro lt.
  generalize (bin_delFMax_decr (Bin s k l1 l2)).
  intro bdf.
  destruct bdf.
  discriminate.
  eauto.
  destruct H.
  destruct H.
  destruct H0.
  rewrite H.
  generalize (size_balanceL x0 x (Bin s0 k0 r1 r2)).
  intro sbl.
  assert (
            (size (balanceL x0 x (Bin s0 k0 r1 r2)) # 1 ==
         1 + (size x # 1) + (size (Bin s0 k0 r1 r2) # 1))%Q
  ).
  apply sbl.
  eauto.
  eauto.
  clear sbl.
  assert (
    (size (balanceL x0 x (Bin s0 k0 r1 r2)) =
        1 + (size x) + (size (Bin s0 k0 r1 r2)))
    ).
  generalize H2; clear.
  compute -[size balanceR Zle Zlt Zplus Zmult].
  psatzl Z.
  rewrite H3.
  rewrite <- H0.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.
  split.
  unfold glue.
  destruct l.
  eauto.
  destruct r.
  eauto.
  case_eq (Zle_bool (size (Bin s k l1 l2)) (size (Bin s0 k0 r1 r2))).
  intro le.
  generalize (bin_delFM_decr (Bin s0 k0 r1 r2)).
  intro decr.
  assert (         exists t' : FSet,
           exists x : K,
             deleteFindMin (Bin s0 k0 r1 r2) = (Some x, t') /\
             size t' + 1 = size (Bin s0 k0 r1 r2) /\ validsize_rec t'
             ).
  apply decr.
  discriminate.
  eauto.
  clear decr.
  destruct H.
  rename x into t'.
  destruct H.
  destruct H.
  destruct H0.
  rewrite H.
  generalize (validsize_balanceR x (Bin s k l1 l2) t').
  intro val.
  apply val.
  eauto.
  auto.
  intro lt.
  generalize (bin_delFMax_decr (Bin s k l1 l2)).
  intro decr.
  assert (
             exists t' : FSet,
           exists x : K,
             deleteFindMax (Bin s k l1 l2) = (Some x, t') /\
             size t' + 1 = size (Bin s k l1 l2) /\ validsize_rec t'
             ).
  apply decr.
  discriminate.
  eauto.
  clear decr.
  destruct H.
  rename x into t'.
  destruct H.
  destruct H.
  destruct H0.
  rewrite H.
  generalize (validsize_balanceL x t' (Bin s0 k0 r1 r2)).
  intro val.
  apply val.
  auto.
  auto.
  unfold glue.
  destruct l.
  auto.
  destruct r.
  auto.
  case_eq (Zle_bool (size (Bin s k l1 l2)) (size (Bin s0 k0 r1 r2))).
  intro le.
  generalize (bin_delFM_decr (Bin s0 k0 r1 r2)).
  intro bdf.
  assert (
            exists t' : FSet,
          exists x : K,
            deleteFindMin (Bin s0 k0 r1 r2) = (Some x, t') /\
            size t' + 1 = size (Bin s0 k0 r1 r2) /\ validsize_rec t'
            ).
  apply bdf.
  discriminate.
  eauto.
  clear bdf.
  destruct H.
  rename x into t'.
  destruct H.
  destruct H.
  destruct H0.
  rewrite H.
  apply balanceR_balance.
  assumption.
  auto.
  auto.
  auto.
  generalize delFMin_balanced.
  intro dfb.
  generalize (dfb (Bin s0 k0 r1 r2)).
  clear dfb.
  intro dfb.
  rewrite H in dfb.
  apply dfb.
  assumption.
  auto.
  auto.
  auto.
  unfold isBalanced in lrbal.
  unfold isBalanced in rlbal.
  rewrite <- H0 in lrbal.
  rewrite <- H0 in rlbal.
  auto.
  unfold isBalanced in lrbal.
  unfold isBalanced in rlbal.
  rewrite <- H0 in lrbal.
  rewrite <- H0 in rlbal.
  auto.
  intro lt.
  generalize (bin_delFMax_decr (Bin s k l1 l2)).
  intro dfd.
  assert (
            exists t' : FSet,
          exists x : K,
            deleteFindMax (Bin s k l1 l2) = (Some x, t') /\
            size t' + 1 = size (Bin s k l1 l2) /\ validsize_rec t').
  apply dfd.
  discriminate.
  eauto.
  clear dfd.
  destruct H.
  rename x into t'.
  destruct H.
  destruct H.
  destruct H0.
  rewrite H.
  generalize (balanceL_balance x t' (Bin s0 k0 r1 r2)).
  intro bgb.
  apply bgb.
  assumption.
  assumption.
  assumption.
  generalize (delFMax_balanced (Bin s k l1 l2)).
  intro dfb.
  rewrite H in dfb.
  apply dfb.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite H0.
  unfold isBalanced in lrbal.
  assumption.
  unfold isBalanced in rlbal.
  rewrite H0.
  assumption.
  Qed.

Fixpoint merge_ (x: FSet) := fix merge_inner (y: FSet) :=
  match x with
    | Tip => y
    | Bin kx sizex lx rx =>
      match y with
        | Tip => x
        | Bin sizey ky ly ry =>
          if isBalanced x y then
            (if isBalanced y x then
              glue x y
              else
                balanceL ky lx (merge_ rx y)
                )
            else
              balanceR ky (merge_inner ly) ry
      end
  end.

Fixpoint delete (kx: K) (t: FSet): FSet :=
  match t with
    | Tip => Tip
    | Bin _ ky l r
          => match X.compare kx ky with
               | LT _ => balanceL kx (delete kx l) r
               | GT _ => balanceR kx l (delete kx r)
               | EQ _ => glue l r
             end
  end.


Lemma delete_balance:
  good_params ->
  forall (x: K) (t: FSet),
    validsize_rec t ->
    Is_true (balanced t) ->
    ((size (delete x t) + 1 = size t) \/ (size (delete x t) = size t))
    /\
    validsize_rec (delete x t) /\
    Is_true (balanced (delete x t)).
  intro gp.
  intros x t.
  induction t.
  intros.
  split.
  right.
  compute.
  trivial.
  split.
  auto.
  compute.
  auto.
  intro vrec.
  intro bal.
  assert (s = 1 + (size t1) + (size t2)).
  assert (validsize (Bin s k t1 t2)).
  eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  clear H.
  unfold realsize; fold realsize.
  assert (realsize t1 = size t1).
  assert (validsize t1); eauto.
  rewrite H.
  clear H.
  assert (realsize t2 = size t2).
  assert (validsize t2); eauto.
  rewrite H.
  clear H.
  reflexivity.
  rewrite H in *.
  clear H s.
  unfold balanced in bal.
  fold balanced in bal.
  apply andb_prop_elim in bal; destruct bal.
  apply andb_prop_elim in H; destruct H.
  apply andb_prop_elim in H; destruct H.
  assert (
         (size (delete x t1) + 1 = size t1 \/ size (delete x t1) = size t1) /\
         validsize_rec (delete x t1) /\ Is_true (balanced (delete x t1))
  ).
  apply IHt1.
  eauto.
  auto.
  clear IHt1.
  destruct H3.
  destruct H4.
  assert (
         (size (delete x t2) + 1 = size t2 \/ size (delete x t2) = size t2) /\
         validsize_rec (delete x t2) /\ Is_true (balanced (delete x t2))
  ).
  apply IHt2.
  eauto.
  auto.
  destruct H6.
  destruct H7.
  clear IHt2.
  split.
  unfold delete.
  fold delete.
  case (X.compare x k).
  intro lt.
  clear  H6 H7 H8 lt.
  destruct H3.
  left.
  generalize (size_balanceL x (delete x t1) t2).
  intro sbg.
  assert (
    (size (balanceL x (delete x t1) t2) # 1 ==
      1 + (size (delete x t1) # 1) + (size t2 # 1))%Q
  ).
  apply sbg.
  auto.
  eauto.
  clear sbg.
  assert (
    (size (balanceL x (delete x t1) t2) =
        1 + (size (delete x t1)) + (size t2))).
  generalize H6.
  clear.
  compute -[Zmult Zle Zplus Zlt balanceL delete size].
  psatzl Z.
  clear H6.
  rewrite H7.
  clear H7.
  unfold size; fold size.
  rewrite <- H3.
  psatzl Z.
  right.
  generalize (size_balanceL x (delete x t1) t2).
  intro sbg.
  assert (
            (size (balanceL x (delete x t1) t2) # 1 ==
         1 + (size (delete x t1) # 1) + (size t2 # 1))%Q
            ).
  apply sbg.
  eauto.
  eauto.
  clear sbg.
  assert (
    (size (balanceL x (delete x t1) t2) =
        1 + (size (delete x t1)) + (size t2))
    ).
  generalize H6.
  clear.
  compute -[Zmult Zle Zplus Zlt size delete balanceL].
  psatzl Z.
  clear H6.
  rewrite H7.
  unfold size; fold size.
  rewrite H3.
  reflexivity.
  intro eq.
  left.
  clear H3.
  clear H4.
  clear H5.
  clear H6.
  clear H7.
  clear H8.
  clear eq.
  generalize (glue_decr gp t1 t2).
  intro gd.
  assert
    (       size (glue t1 t2) = size t1 + size t2 /\
       validsize_rec (glue t1 t2) /\ Is_true (balanced (glue t1 t2))
       ).
  apply gd.
  eauto.
  eauto.
  auto.
  auto.
  auto.
  auto.
  clear gd.
  unfold size; fold size.
  destruct H3.
  rewrite H3.
  psatzl Z.
  intro lt.
  clear H3 H4 H5.
  destruct H6.
  left.
  generalize (size_balanceR x t1 (delete x t2)).
  intro sbl.
  assert (
            (size (balanceR x t1 (delete x t2)) # 1 ==
         1 + (size t1 # 1) + (size (delete x t2) # 1))%Q
            ).
  apply sbl.
  eauto.
  eauto.
  clear sbl.
  assert (
    (size (balanceR x t1 (delete x t2)) =
        1 + (size t1) + (size (delete x t2)))
    ).
  generalize H4; clear.
  compute -[Zmult Zplus Zle delete balanceR size].
  psatzl Z.
  clear H4.
  rewrite H5.
  clear H5.
  unfold size; fold size.
  rewrite <- H3.
  psatzl Z.
  right.
  generalize (size_balanceR x t1 (delete x t2)).
  intro sbl.
  assert (
            (size (balanceR x t1 (delete x t2)) # 1 ==
         1 + (size t1 # 1) + (size (delete x t2) # 1))%Q
).
  apply sbl.
  eauto.
  auto.
  clear sbl.
  assert (
    (size (balanceR x t1 (delete x t2)) =
        1 + (size t1 ) + (size (delete x t2)))).
  generalize H4.
  clear.
  compute -[Zmult Zle Zplus Zlt size balanceR delete].
  psatzl Z.
  clear H4.
  rewrite H5.
  clear H5.
  unfold size; fold size.
  rewrite H3.
  reflexivity.
  split.
  unfold delete.
  fold delete.
  case (X.compare x k).
  intro lt.
  apply validsize_balanceL.
  auto.
  eauto.
  intro eq.
  eapply glue_decr.
  auto.
  eauto.
  eauto.
  auto.
  auto.
  auto.
  auto.
  intro lt.
  apply validsize_balanceR.
  eauto.
  auto.
  unfold delete.
  fold delete.
  case (X.compare x k).
intro lt.
clear H6 H7 H8.
destruct H3.
apply balanceL_balance.
auto.
auto.
eauto.
auto.
auto.
rewrite H3.
auto.
rewrite H3.
auto.
unfold balanceL.
assert (Is_true (isBalanced (delete x t1) t2)).
unfold isBalanced.
rewrite H3.
unfold isBalanced in H.
assumption.
case_eq (isBalanced (delete x t1) t2).
intro bal.
clear bal.
unfold bin.
unfold balanced; fold balanced.
repeat (apply andb_prop_intro ; intuition).
unfold isBalanced.
rewrite H3.
unfold isBalanced in *.
assumption.
intro f.
rewrite f in H6.
apply False_ind.
generalize H6.
clear.
intuition.
intro eq.
eapply glue_decr.
assumption.
eauto.
eauto.
auto.
auto.
auto.
auto.
clear H3.
clear H4.
clear H5.
intro lt.
destruct H6.
apply balanceR_balance.
auto.
auto.
eauto.
auto.
auto.
unfold isBalanced in *.
rewrite H3.
auto.
unfold isBalanced in *.
rewrite  H3.
auto.
unfold balanceR.
case_eq (isBalanced (delete x t2) t1).
intro bal.
unfold bin.
rewrite H3.
unfold balanced.
fold balanced.
repeat (apply andb_prop_intro; intuition).
unfold isBalanced in *.
rewrite H3.
auto.
intro f.
apply False_ind.
unfold isBalanced in *.
rewrite H3 in f.
rewrite f in H2.
generalize H2; clear; intuition.
Qed.

(* this is the second program lemma *)
Lemma delete_balanced:
  good_params ->
  forall (t: FSet) (k: K),
    balance_rec t -> validsize_rec t -> balance_rec (delete k t).
  intro gp.
  intros x t.
  intros.
  generalize delete_balance.
  intro db.
  destruct db with t x.
  assumption.
  eauto.
  eauto.
  unfold balance_rec.
  eapply H2.
  Qed.


(*************************************************
   Part 3: program lemmas.
   union, difference and intersectino keep balance
   under <3,2>
**************************************************)


Fixpoint join (x: K) (l: FSet) := fix join_inner (r: FSet) :=
  match l with
    | Tip => insert x r
    | Bin sizeL y ly ry =>
      match r with
        | Tip => insert x l
        | Bin sizeR z lz rz =>
          if isBalanced l r then
            (if isBalanced r l then bin x l r
             else balanceL y ly (join x ry r))
            else
              balanceR z (join_inner lz) rz
      end
  end.

Lemma size_insertZ:
  forall (x:K) (t:FSet),
  validsize_rec t ->
  ((size (insert x t)) = 1 + size t
    \/
    (size (insert x t)) = size t).
  intros.
  generalize (size_insert x t).
  intro.
  apply H0 in H.
  clear H0.
  destruct H.
  left.
  generalize H.
  clear.
  compute -[Zmult Zplus Zle Zlt size insert].
  psatzl Z.
  right.
  generalize H.
  clear.
  compute -[Zmult Zplus Zle Zlt size insert].
  psatzl Z.
  Qed.

  Lemma validsize_Bin:
    forall (l1 l2: FSet) (s: Size) (x: K),
      validsize_rec (Bin s x l1 l2) ->
      s = size l1 + size l2 + 1.
  intros l1 l2 s x.
  intro vrec.
  assert (validsize (Bin s x l1 l2)); eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  clear H.
  unfold realsize.
  fold realsize.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  generalize (realsize l1).
  generalize (realsize l2).
  intros.
  rewrite Zplus_comm.
  rewrite Zplus_assoc.
  rewrite Zplus_comm.
  rewrite Zplus_assoc.
  reflexivity.
  assert (validsize l2); eauto.
  assert (validsize l1); eauto.
  Qed.


Lemma validsize_rec_rotateR:
  forall (x: K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
     validsize_rec (rotateR x l r).
  intros x l r.
  intros vrecl vrecr.
  unfold rotateR.
  destruct l.
  unfold assert_false.
  apply validsize_rec_bin.
  intuition.
  auto.
  case (isSingle l2 l1).
  unfold singleR.
  apply validsize_rec_bin.
  eauto.
  apply validsize_rec_bin.
  eauto.
  auto.
  unfold doubleR.
  destruct l2.
  unfold assert_false.
  apply validsize_rec_bin.
  unfold validsize_rec; fold validsize_rec.
  split.
  eauto.
  eauto.
  auto.
  apply validsize_rec_bin.
  apply validsize_rec_bin.
  eauto.
  eauto.
  apply validsize_rec_bin.
  eauto.
  auto.
  Qed.

Lemma validsize_rec_rotateL:
  forall (x: K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    validsize_rec (rotateL x l r).
  intros x l r.
  intros vrecl vrecr.
  unfold rotateL.
  destruct r.
  unfold assert_false.
  apply validsize_rec_bin; auto.
  case (isSingle r1 r2).
  unfold singleL.
  apply validsize_rec_bin.
  apply validsize_rec_bin.
  auto.
  eauto.
  eauto.
  unfold doubleL.
  destruct r1.
  unfold assert_false.
  apply validsize_rec_bin.
  auto.
  auto.
  apply validsize_rec_bin.
  apply validsize_rec_bin.
  auto.
  eauto.
  eauto.
  Qed.

Lemma size_binZ:
  forall (x: K) (l r: FSet),
    size (bin x l r) = 1 + size l + size r.
  intros x l r.
  unfold bin.
  unfold size.
  fold size.
  reflexivity.
  Qed.

Lemma size_rotateRZ:
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    (size (rotateR x l r) =
      1 + size l + size r).
  intros x l r.
  intros val var.
  unfold rotateR.
  destruct l.
  unfold assert_false.
  unfold bin.
  unfold size.
  fold size.
  reflexivity.
  case (isSingle l2 l1).
  unfold singleR.
  rewrite size_binZ.
  rewrite size_binZ.
  replace (size (Bin s k l1 l2)) with
    (1 + size l1 + size l2).
  unfold Size in *.
  psatzl Z.
  assert (validsize (Bin s k l1 l2)).
  eauto.
  unfold validsize in H.
  rewrite <- H.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  reflexivity.
  assert (validsize l2); eauto.
  assert (validsize l1); eauto.

  unfold doubleR.
  destruct l2.
  unfold assert_false.
  rewrite size_binZ.
  reflexivity.

  rewrite size_binZ.
  rewrite size_binZ.
  rewrite size_binZ.
  unfold size.
  fold size.
  replace s with ((1 + size l1 + size l2_1) + (1 + size l2_2)).
  unfold Size in *.
  psatzl Z.
  replace s with
    (1 + size l1 + size ((Bin s0 k0 l2_1 l2_2))).
  unfold size; fold size.
  replace s0 with
    (1 + size l2_1 + size l2_2).
  psatzl Z.
  erewrite validsize_Bin.
  Focus 2.
  eauto.
  Unfocus.
  psatzl Z.
  erewrite validsize_Bin.
  Focus 2.
  eauto.
  Unfocus.
  psatzl Z.
  Qed.

Lemma size_balanceRZ:
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    size (balanceR x l r) = size l + size r + 1.
  intros x l r.
  intros val var.
  unfold balanceR.
  case (isBalanced r l).
  unfold bin.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.
  rewrite size_rotateRZ.
  unfold Size in *.
  psatzl Z.
  auto.
  auto.
  Qed.
              
Lemma size_rotateLZ:
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    (size (rotateL x l r) =
      1 + size l + size r).
  intros x l r.
  intros vrecl vrecr.
  unfold rotateL.
  destruct r.
  unfold assert_false.
  rewrite size_binZ.
  reflexivity.
  case (isSingle r1 r2).
  unfold singleL.
  rewrite size_binZ.
  rewrite size_binZ.
  unfold size.
  fold size.
  replace s with (size r1 + size r2 + 1).
  unfold Size in *.
  psatzl Z.
  assert (validsize (Bin s k r1 r2)).
  eauto.
  unfold validsize in H.
  unfold size in H.
  unfold realsize in H.
  fold realsize in H.
  rewrite <- H.
  replace (size r1) with (realsize r1).
  replace (size r2) with (realsize r2).
  psatzl Z.
  assert (validsize r2); eauto.
  assert (validsize r1); eauto.

  unfold doubleL.
  destruct r1.
  unfold assert_false.
  repeat rewrite size_binZ.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.
  repeat rewrite size_binZ.
  unfold size; fold size.
  replace s with (
    size (Bin s0 k0 r1_1 r1_2) + size r2 + 1).
  unfold size.
  fold size.
  replace s0 with
    (size r1_1 + size r1_2 + 1).
  unfold Size in *.
  psatzl Z.
  assert (validsize (Bin s0 k0 r1_1 r1_2)).
  eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  clear H.
  unfold realsize.
  fold realsize.
  replace (size r1_1) with (realsize r1_1).
  replace (size r1_2) with (realsize r1_2).
  psatzl Z.
  assert (validsize r1_2); eauto.
  assert (validsize r1_1); eauto.
  unfold size.
  fold size.
  assert (validsize (Bin s k (Bin s0 k0 r1_1 r1_2) r2)).
  eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  clear H.
  unfold realsize.
  fold realsize.
  replace s0 with
    (size r1_1 + size r1_2 + 1).
  replace (size r1_1) with
    (realsize r1_1).
  replace (size r1_2) with
    (realsize r1_2).
  replace (size r2) with
    (realsize r2).
  psatzl Z.
  assert (validsize r2); eauto.
  assert (validsize r1_2); eauto.
  assert (validsize r1_1); eauto.

  assert (validsize ((Bin s0 k0 r1_1 r1_2))).
  eauto.
  unfold validsize in H.
  unfold size in H.
  rewrite <- H.
  clear H.
  unfold realsize.
  fold realsize.
  replace (size r1_1) with (realsize r1_1).
  replace (size r1_2) with (realsize r1_2).
  psatzl Z.

  assert (validsize r1_2); eauto.
  assert (validsize r1_1); eauto.
  Qed.
  

Lemma size_balanceLZ:
  forall (x:K) (l r: FSet),
    validsize_rec l -> validsize_rec r ->
    size (balanceL x l r) = size l + size r + 1.
  intros x l r.
  intros vrecl vrecr.
  unfold balanceL.
  case (isBalanced l r).
  rewrite size_binZ.
  unfold Size in *.
  psatzl Z.
  rewrite size_rotateLZ.
  unfold Size in *.
  psatzl Z.
  assumption.
  assumption.
  Qed.

Lemma join_size:
  good_params ->
  forall (x: K) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    (validsize_rec (join x l r) /\
     (
    (size (join x l r) = (size l) + (size r) + 1 \/
     size (join x l r) = (size l) + (size r)))).
  intro gp.
  intros x l r.
  intros vrecl vrecr.
  generalize dependent r.
  induction l.
  intro r.
  intro vrecr.
  induction r.

  (* Tip Tip *)
  unfold join.
  unfold insert.
  unfold singleton.
  unfold size.
  split.
  compute.
  intuition.
  left.
  compute.
  reflexivity.

  (* Tip Bin *)
  unfold join.
  generalize (size_insertZ x (Bin s k r1 r2)).
  intro si.
  split.
  apply validsize_insert.
  eauto.
  assert (
           size (insert x (Bin s k r1 r2)) = 1 + size (Bin s k r1 r2) \/
       size (insert x (Bin s k r1 r2)) = size (Bin s k r1 r2)
       ) as si_now.
  apply si.
  eauto.
  clear si.
  destruct si_now.
  rewrite H.
  left.
  unfold size.
  unfold Size in *.
  psatzl Z.
  rewrite H.
  clear H.
  right.
  unfold size.
  unfold Size in *.
  psatzl Z.

  (* left is Bin *)
  assert (
         forall r : FSet,
         validsize_rec r ->
         validsize_rec (join x l1 r) /\
         (size (join x l1 r) = size l1 + size r + 1 \/
          size (join x l1 r) = size l1 + size r)
         ) as IHll.
  apply IHl1.
  eauto.
  clear IHl1.
  assert (
         forall r : FSet,
         validsize_rec r ->
         validsize_rec (join x l2 r) /\
         (size (join x l2 r) = size l2 + size r + 1 \/
          size (join x l2 r) = size l2 + size r)
         ) as IHlr.
  apply IHl2.
  eauto.
  clear IHl2.
  induction r.
  intro vtip.
  unfold join.
  split.
  apply validsize_insert.
  auto.
  generalize (size_insertZ x (Bin s k l1 l2)).
  intro si.
  assert (
           size (insert x (Bin s k l1 l2)) = 1 + size (Bin s k l1 l2) \/
       size (insert x (Bin s k l1 l2)) = size (Bin s k l1 l2)
       ) as si_now.
  apply si.
  eauto.
  
  clear si.
  destruct si_now.
  left.
  generalize H.
  clear.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.
  right.
  generalize H.
  clear.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  (* Bin Bin *)
  intro vrecr.
  assert (
         validsize_rec (join x (Bin s k l1 l2) r1) /\
         (size (join x (Bin s k l1 l2) r1) =
          size (Bin s k l1 l2) + size r1 + 1 \/
          size (join x (Bin s k l1 l2) r1) = size (Bin s k l1 l2) + size r1)
    ) as IHrl.
  apply IHr1.
  eauto.
  clear IHr1.
  assert (
         validsize_rec (join x (Bin s k l1 l2) r2) /\
         (size (join x (Bin s k l1 l2) r2) =
          size (Bin s k l1 l2) + size r2 + 1 \/
          size (join x (Bin s k l1 l2) r2) = size (Bin s k l1 l2) + size r2)
    ) as IHrr.
  apply IHr2.
  eauto.
  clear IHr2.
  assert (validsize_rec (Bin s k l1 l2)) as s_red.
  assumption.
  apply validsize_Bin in s_red.
  rewrite s_red in *.
  clear s s_red.
  assert (validsize_rec (Bin s0 k0 r1 r2)) as s0_red.
  assumption.
  apply validsize_Bin in s0_red.
  rewrite s0_red in *.
  clear s0 s0_red.
  
  unfold join.
  fold join.
  case_eq (isBalanced (Bin (size l1 + size l2 + 1) k l1 l2)
           (Bin (size r1 + size r2 + 1) k0 r1 r2)).
  intro ballr.
  case_eq (isBalanced (Bin (size r1 + size r2 + 1) k0 r1 r2)
           (Bin (size l1 + size l2 + 1) k l1 l2)).
  intro balrl.

  split.
  apply validsize_rec_bin; assumption.
  
  unfold bin.
  unfold size.
  fold size.
  left.
  unfold Size in *.
  psatzl Z.

  intro unbalrl.
  unfold balanceL.
  case_eq (isBalanced l1 (join x l2 (Bin (size r1 + size r2 + 1) k0 r1 r2))).

  intro ball1.
  split.
  apply validsize_rec_bin; eauto.
  eapply IHlr.
  auto.
  
  unfold bin.
  unfold size.
  fold size.
  elim IHlr with (Bin (size r1 + size r2 + 1) k0 r1 r2).
  intro vrec.
  intro ih.
  destruct ih as [ih | ih].
  rewrite ih.
  clear ih.
  unfold size.
  fold size.
  left.
  unfold Size in *.
  psatzl Z.

  rewrite ih.
  clear ih.
  right.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  auto.

  split.
  apply validsize_rec_rotateL.
  eauto.
  eapply IHlr.
  eauto.

  rewrite size_rotateLZ.
  elim IHlr with (Bin (size r1 + size r2 + 1) k0 r1 r2).
  intro ih.
  intro ih2.
  destruct ih2.
  rewrite H0.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  rewrite H0.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  auto.
  eauto.

  eapply IHlr.
  auto.

  intro unbal.
  split.

  unfold balanceR.
  case (isBalanced r2
           ((fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert x (Bin (size l1 + size l2 + 1) k l1 l2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) r
                   then
                    if isBalanced r (Bin (size l1 + size l2 + 1) k l1 l2)
                    then bin x (Bin (size l1 + size l2 + 1) k l1 l2) r
                    else balanceL k l1 (join x l2 r)
                   else
                    if isBalanced rz (join_inner lz)
                    then bin z (join_inner lz) rz
                    else rotateR z (join_inner lz) rz
               end) r1)).
  apply validsize_rec_bin.
  unfold join in IHrl.
  fold join in IHrl.
  destruct IHrl.
  clear H0.
  assumption.
  eauto.

  apply validsize_rec_rotateR.
  destruct IHrl.
  clear H0.
  unfold join in H.
  fold join in H.
  assumption.
  eauto.

  unfold balanceR.
  case_eq (isBalanced r2
           ((fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert x (Bin (size l1 + size l2 + 1) k l1 l2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) r
                   then
                    if isBalanced r (Bin (size l1 + size l2 + 1) k l1 l2)
                    then bin x (Bin (size l1 + size l2 + 1) k l1 l2) r
                    else balanceL k l1 (join x l2 r)
                   else
                    if isBalanced rz (join_inner lz)
                    then bin z (join_inner lz) rz
                    else rotateR z (join_inner lz) rz
               end) r1)).
  intro bal.
  rewrite size_binZ.
  clear bal.
  clear IHrr.
  destruct IHrl.
  clear H.
  unfold join in H0.
  fold join in H0.

  destruct H0.

  case_eq r1.
  intro tip.
  rewrite tip in H.
  rewrite H.
  unfold size.
  fold size.

  unfold Size in *.
  psatzl Z.

  intros s k1 f f0.
  intro r1eq.
  rewrite r1eq in *.

  case_eq (isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) (Bin s k1 f f0)).
  intro bal.
  rewrite bal in *.
  rewrite H.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  intro ununbal.
  rewrite ununbal in *.
  unfold balanceR in H.

  case_eq (isBalanced f0
           ((fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert x (Bin (size l1 + size l2 + 1) k l1 l2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) r
                   then
                    if isBalanced r (Bin (size l1 + size l2 + 1) k l1 l2)
                    then bin x (Bin (size l1 + size l2 + 1) k l1 l2) r
                    else balanceL k l1 (join x l2 r)
                   else
                    if isBalanced rz (join_inner lz)
                    then bin z (join_inner lz) rz
                    else rotateR z (join_inner lz) rz
               end) f)).
  intro unbbal.
  rewrite unbbal in *.
  move H at bottom.
  rewrite H.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  intro unununbal.
  move H at bottom.
  rewrite unununbal in H.
  rewrite H.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  case_eq r1.
  intro tip.
  rewrite tip in H.
  rewrite H.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  intros s k1 f f0.
  intro r1bin.
  rewrite r1bin in H.
  case_eq (isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) (Bin s k1 f f0)).
  intro isb.
  rewrite isb in H.

  case_eq (isBalanced (Bin s k1 f f0) (Bin (size l1 + size l2 + 1) k l1 l2)).
  intro isbb.
  rewrite isbb in H.
  rewrite H.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  intro unb.
  rewrite unb in H.
  rewrite H.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  intro unb.
  rewrite unb in H.
  unfold balanceR in H.
  case_eq (isBalanced f0
           ((fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert x (Bin (size l1 + size l2 + 1) k l1 l2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) r
                   then
                    if isBalanced r (Bin (size l1 + size l2 + 1) k l1 l2)
                    then bin x (Bin (size l1 + size l2 + 1) k l1 l2) r
                    else balanceL k l1 (join x l2 r)
                   else
                    if isBalanced rz (join_inner lz)
                    then bin z (join_inner lz) rz
                    else rotateR z (join_inner lz) rz
               end) f)).
  intro henb.
  rewrite henb in H.
  rewrite H.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  intro ununb.
  rewrite ununb in H.
  rewrite H.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  intro ununb.
  rewrite size_rotateRZ.
  unfold join in IHrl.
  fold join in IHrl.
  move IHrl at bottom.
  destruct IHrl.
  destruct H0.

  case_eq r1.
  intro r1tip.
  rewrite r1tip in H0.
  rewrite H0.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.
  intros s k1 f f0.
  intro r1bin.
  rewrite r1bin in H0.

  case_eq (isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) (Bin s k1 f f0)).
  intro bal.
  rewrite bal in H0.
  rewrite H0.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  intro uubal.
  rewrite uubal in H0.
  unfold balanceR in H0.
  rewrite H0.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  case_eq r1.
  intro tip.
  rewrite tip in H0.
  rewrite H0.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  intros s k1 f f0.
  intro r1bin.
  rewrite r1bin in H0.
  case_eq (isBalanced (Bin (size l1 + size l2 + 1) k l1 l2) (Bin s k1 f f0)).
  intro bal.
  rewrite bal in H0.
  rewrite H0.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  intro uubal.
  rewrite uubal in H0.
  unfold balanceR in H0.
  rewrite H0.
  unfold size; fold size.
  unfold Size in *.
  psatzl Z.

  destruct IHrl.
  unfold join in H.
  move H at bottom.
  fold join in H.
  assumption.

  eauto.
  Qed.

Definition p32 :=
  deltaU = 3 /\ deltaD = 1 /\
  ratioU = 2 /\ ratioD = 1.

Lemma good32 :
  p32 -> good_params.
  unfold p32.
  intuition.
  generalize delta_eq.
  rewrite H0.
  rewrite H.
  intro del.
  generalize ratio_eq.
  rewrite H1.
  rewrite H3.
  intro rat.
  unfold good_params.
  clear H0 H1 H3 H.
  intuition.
  unfold normal.
  split.
  psatzl Q.
  split.
  psatz Q.
  psatzl Q.

  unfold slope.
  psatzl Q.

  unfold curve.
  psatz Q.

  unfold deltasup.
  psatz Q.

  unfold ceilA.
  psatz Q.

  unfold ceilB.

  psatz Q.

  unfold ceilC.
  psatz Q.
  unfold ceilD.
  psatz Q.
  Qed.


Lemma size_nnegZ: forall t: FSet,
  validsize t ->
  0 <= size t.
  intro t.
  unfold validsize.
  intro rs.
  rewrite <- rs.
  clear rs.
  induction t.
  intuition.
  unfold realsize.
  fold realsize.
  psatz Z.
  Qed.

Lemma join_balanced:
  forall (l r: FSet) (kx: K),
    p32 ->
    Is_true (balanced l) -> validsize_rec l ->
    Is_true (balanced r) -> validsize_rec r ->
    Is_true (balanced (join kx l r)).
Proof.
  intros l r kx.
  intro p.
  generalize r.
  clear r.
  induction l.

  (* left is Tip *)
  intro r.
  intro baltip.
  clear baltip.
  intro vtip.
  clear vtip.
  induction r.

  (* Tip Tip *)
  intro baltip.
  clear baltip.
  intro vtip.
  clear vtip.
  unfold join.
  apply insert_balanced.
  apply good32.
  assumption.
  compute.
  auto.
  compute.
  reflexivity.

  (* Tip Bin *)
  intro rbal.
  intro rv.
    (* activate IH *)
    assert (Is_true (balanced r1)).
    eapply NR_S_balanced.
    eauto.
    eapply NR_S_balanced in rbal.
    eauto.
    unfold NRbalanced in rbal.
    intuition.
    apply IHr1 in H.
    unfold join.
    apply insert_balanced.
    apply good32.
    assumption.
    eauto.
    eauto.
    eauto.

  (* Left is Bin *)
  induction r.

  (* Bin Tip *)
    intro lbal.
    intro lvr.
    intro tbal.
    clear tbal.
    intro vtip.
    clear vtip.
    unfold join.
    apply insert_balanced.
    apply good32.
    assumption.
    auto.
    auto.

  (* Bin Bin *)
  intro lbal.
  intuition.
  assert (s = size l1 + size l2 + 1) as s_eq.
  assert (validsize (Bin s k l1 l2)).
  eauto.
  unfold validsize in H3.
  unfold realsize in H3.
  fold realsize in H3.
  unfold size in H3.
  rewrite <- H3.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  unfold Size in *.
  psatzl Z.

  assert (validsize l2) ;eauto.
  assert (validsize l1) ;eauto.

  assert (s0 = size r1 + size r2 + 1) as s0_eq.
  assert (validsize (Bin s0 k0 r1 r2)).
  eauto.
  unfold validsize in H3.
  unfold realsize in H3.
  unfold size in H3.
  fold realsize in H3.
  rewrite <- H3.
  replace (size r1) with (realsize r1).
  replace (size r2) with (realsize r2).
  unfold Size in *.
  psatzl Z.

  assert (validsize r2); eauto.
  assert (validsize r1); eauto.

  unfold Size in *.

  assert (0 <= size l1) as l1nneg.
  apply size_nnegZ.
  eauto.

  assert (0 <= size l2) as l2nneg.
  apply size_nnegZ.
  eauto.

  assert (0 <= size r1) as r1nneg.
  apply size_nnegZ.
  eauto.
  
  assert (0 <= size r2) as r2nneg.
  apply size_nnegZ.
  eauto.

  assert (
    Is_true (balanced (join kx (Bin s k l1 l2) r1)) ) as IHr1.
  apply H4.
  eapply NR_S_balanced.
  eapply NR_S_balanced in lbal.
  eauto.
  eauto.
  eapply NR_S_balanced in H0.
  eauto.
  unfold NRbalanced in H0.
  tauto.
  eauto.
  clear H4.

  assert (
    Is_true (balanced (join kx (Bin s k l1 l2) r2)))
  as IHr2.
  apply H2.
  eapply NR_S_balanced.
  eapply NR_S_balanced in H0.
  eauto.
  eauto.
  eapply NR_S_balanced in H0.
  eauto.
  unfold NRbalanced in H0.
  tauto.

  eauto.

  unfold balanced in *.
  fold balanced.
  fold balanced in IHr1.
  fold balanced in IHr2.
  fold balanced in H2.
  fold balanced in H0.
  fold balanced in IHl2.
  fold balanced in IHl1.
  fold balanced in lbal.
  apply andb_prop_elim in H0.
  apply andb_prop_elim in lbal.
  destruct lbal.
  destruct H0.
  apply andb_prop_elim in H3.
  apply andb_prop_elim in H0.
  destruct H0.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H0.
  destruct H0.

  assert (Is_true (balanced r2)).
  assumption.
  apply H2 in H10.
  clear H2.
  Focus 2.
  eauto.
  Unfocus.

  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  apply Is_true_eq_true in H3.
  apply Is_true_eq_true in H8.
  apply Is_true_eq_true in H0.
  apply Is_true_eq_true in H9.

  apply Zle_bool_imp_le in H3.
  apply Zle_bool_imp_le in H8.
  apply Zle_bool_imp_le in H0.
  apply Zle_bool_imp_le in H9.

  unfold p32 in *.
  destruct p.
  destruct H11.
  destruct H12.
  rewrite H2 in *.
  rewrite H11 in *.
  clear H10.

  unfold join.
  fold join.
  
  case_eq (isBalanced (Bin s k l1 l2) (Bin s0 k0 r1 r2)).
  intro bal.
  case_eq (isBalanced (Bin s0 k0 r1 r2) (Bin s k l1 l2)).
  intro bbal.
  
  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.

  apply Zle_bool_imp_le in bal.
  apply Zle_bool_imp_le in bbal.

  rewrite H2 in *.
  rewrite H11 in *.
  
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  assumption.
  assumption.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  assumption.
  assumption.

  intro unb.
  unfold isBalanced in bal.
  unfold isBalanced in unb.
  unfold isBalancedSizeZ in *.
  apply Zle_bool_imp_le in bal.

  case (Z_gt_le_dec
    (deltaD * (size (Bin s k l1 l2) + 1))
          (deltaU * (size (Bin s0 k0 r1 r2) + 1))).
  intro gt.
  clear unb.

  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.
  Unfocus.

  unfold balanceL.
  case_eq (isBalanced l1 (join kx l2 (Bin s0 k0 r1 r2))).
  intro balt.
  unfold isBalanced in balt.
  unfold isBalancedSizeZ in balt.
  apply Zle_bool_imp_le in balt.

  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.

  rewrite H2 in *.
  rewrite H11 in *.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatz Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  generalize join_size.
  intro js.
  elim js with kx l2 (Bin s0 k0 r1 r2).
  intro vrecj.
  clear js.
  intro sjoin.
  destruct sjoin as [sjoin | sjoin].
  rewrite sjoin.
  
  unfold size.
  fold size.

  psatzl Z.

  rewrite sjoin.
  unfold size; fold size.
  rewrite s_eq in *.
  rewrite s0_eq in *.
  clear s s0 s_eq s0_eq.
  rewrite sjoin in balt.

  unfold size in balt.
  fold size in balt.
  unfold size in gt.
  fold size in gt.
  unfold size in bal.
  fold size in bal.

  psatzl Z.

  apply good32.
  unfold p32.
  intuition.

  eauto.
  eauto.
  eauto.

  unfold size in bal.
  unfold size in gt.

  eapply IHl2.
  auto.
  eauto.

  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.

  rewrite H2 in *.
  rewrite H11 in *.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  assumption.
  assumption.

  eauto.

  (* intermediate point *)
  rewrite H2 in *.
  rewrite H11 in *.
  unfold size in bal.
  unfold size in gt.

  intro unb.
  unfold isBalanced in unb.
  unfold isBalancedSizeZ in unb.

  case (Z_le_gt_dec (deltaD * (size (join kx l2 (Bin s0 k0 r1 r2)) + 1))
          (deltaU * (size l1 + 1))).
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.

  clear unb.
  intro unb.
  rewrite H2 in unb.
  rewrite H11 in unb.

  unfold rotateL.

  case_eq (join kx l2 (Bin s0 k0 r1 r2)).
  intro jtip.
  rewrite jtip in *.
  unfold size in unb.
  fold size in unb.
  apply False_ind.
  psatzl Z.

  intros s1 k1 f f0.
  intro jlr.

  assert (Is_true (balanced (Bin s1 k1 f f0))) as jbal.
  rewrite <- jlr.
  apply IHl2.
  eauto.
  eauto.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  auto.
  auto.
  eauto.

  assert (validsize_rec (Bin s1 k1 f f0)) as vrecff0.
  rewrite <- jlr.
  eapply join_size.
  apply good32.
  unfold p32.
  intuition.
  eauto.
  eauto.

  unfold balanced in jbal.
  fold balanced in jbal.
  apply andb_prop_elim in jbal.
  destruct jbal as [jbal f0bal].
  apply andb_prop_elim in jbal.
  destruct jbal as [jbal fbal].
  apply andb_prop_elim in jbal.
  destruct jbal as [ff0 f0f].

  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite H2 in *.
  rewrite H11 in *.
  apply Is_true_eq_true in ff0.
  apply Is_true_eq_true in f0f.
  apply Zle_bool_imp_le in ff0.
  apply Zle_bool_imp_le in f0f.
  
  assert (s1 = size f + size f0 + 1) as s1_eq.
  assert (validsize (Bin s1 k1 f f0)).
  rewrite <- jlr.
  apply validsize_rec_self.
  eapply join_size.
  apply good32.
  unfold p32.
  intuition.
  eauto.
  eauto.
  unfold validsize in H10.
  unfold size in H10.
  rewrite <- H10.
  unfold realsize.
  fold realsize.
  replace (size f) with (realsize f).
  replace (size f0) with (realsize f0).
  unfold Size in *.
  psatzl Z.

  assert (validsize f0); eauto.
  assert (validsize f); eauto.

  case_eq (isSingle f f0).
  intro single.
  unfold isSingle in single.
  unfold isSingleSizeP in single.
  unfold singleL.
  unfold bin.
  unfold balanced.
  fold balanced.

  rewrite H12 in *.
  rewrite H13 in *.
  eapply Zgt_is_gt_bool in single.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold size; fold size.

  (* use join_size *)
  generalize join_size.
  intro js.
  elim js with kx l2 (Bin s0 k0 r1 r2).
  clear js.
  intro vrec.
  intro sj.
  rewrite jlr in vrec.
  rewrite jlr in sj.
  unfold size in sj.
  fold size in sj.
  rewrite jlr in unb.
  unfold size in unb.
  fold size in unb.

  unfold Size in *.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  destruct sj.
  psatzl Z.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  auto.

  apply good32.
  unfold p32.
  intuition.

  eauto.
  eauto.


  intro double.
  unfold isSingle in double.
  unfold isSingleSizeP in double.
  rewrite H12 in double.
  rewrite H13 in double.

  case (Z_gt_le_dec (2 * (size f0 + 1)) (1 * (size f + 1))).
  intro ggt.
  eapply Zgt_is_gt_bool in ggt.
  rewrite ggt in double.
  apply False_ind.
  clear - double.
  discriminate.

  clear double.
  intro double.

  unfold doubleL.
  destruct f.
  unfold assert_false.
  unfold size in double.
  fold size in double.
  clear fbal.
  unfold bin.
  unfold size.
  fold size.

  apply False_ind.
  generalize (size_nnegZ f0).
  intro snneg.

  assert (validsize f0).
  eauto.
  apply snneg in H10.
  clear snneg.
  psatzl Z.

  unfold size in s1_eq.
  fold size in s1_eq.

  assert (s2 = size f1 + size f2 + 1) as se_eq.
  assert (validsize (Bin s2 k2 f1 f2)).
  eauto.
  unfold validsize in H10.
  unfold size in H10.
  rewrite <- H10.
  clear H10.
  unfold realsize.
  fold realsize.
  replace (size f1) with (realsize f1).
  replace (size f2) with (realsize f2).
  unfold Size in *.
  psatzl Z.
  assert (validsize f2); eauto.
  assert (validsize f1); eauto.

  rename se_eq into s2_eq.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold size.
  fold size.

  unfold balanced in fbal.
  fold balanced in fbal.
  apply andb_prop_elim in fbal.
  destruct fbal.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  unfold isBalanced in H10.
  unfold isBalanced in H16.
  unfold isBalancedSizeZ in *.
  rewrite H2 in *.
  rewrite H11 in *.
  apply Is_true_eq_true in H10.
  apply Is_true_eq_true in H16.
  apply Zle_bool_imp_le in H10.
  apply Zle_bool_imp_le in H16.

  unfold size in double.
  fold size in double.
  unfold size in ff0.
  fold size in ff0.
  unfold size in f0f.
  fold size in f0f.

  rewrite jlr in *.
  unfold size in unb.
  fold size in unb.

  rewrite s_eq in *.
  clear s s_eq.
  rewrite s2_eq in *.
  clear s2 s2_eq.
  rewrite s1_eq in *.
  clear s1 s1_eq.
  rewrite s0_eq in *.
  clear s0 s0_eq.

  (* show iroiro >= 0 *)
  generalize (size_nnegZ f0).
  generalize (size_nnegZ f1).
  generalize (size_nnegZ f2).
  intro sf2.
  intro sf1.
  intro sf0.
  assert (validsize f0).
  eauto.
  apply sf0 in H17.
  clear sf0.
  assert (validsize f1).
  eauto.
  apply sf1 in H18.
  clear sf1.
  assert (validsize f2).
  eauto.
  apply sf2 in H19.
  clear sf2.

  (* join increases size by one at most *)
  generalize join_size.
  intro js.
  elim js with kx l2 (Bin (size r1 + size r2 + 1) k0 r1 r2).
  clear js.
  intro vrecj.
  rewrite jlr in vrecj.
  clear vrecj.
  intro sizej.
  rewrite jlr in sizej.
  unfold size in sizej.
  fold size in sizej.

  (* IHr1 and IHr2 can yield more inequalities *)

  unfold Size in *.
  

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  auto.
  auto.

  apply good32.
  unfold p32.
  intuition.

  eauto.
  eauto.

  (* half ended! *)
  intro unb.
  unfold isBalanced in unb.
  unfold isBalancedSizeZ in unb.
  case (Z_le_gt_dec (deltaD * (size (Bin s0 k0 r1 r2) + 1))
          (deltaU * (size (Bin s k l1 l2) + 1)) ).
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.

  clear unb.
  intro unb.
  unfold size in unb.
  fold size in unb.
  rewrite H2 in *.
  rewrite H11 in *.

  unfold join in IHr1.
  fold join in IHr1.

  generalize (join_size).
  intro js.
  elim js with kx (Bin s k l1 l2) r1.
  clear js.
  unfold join.
  fold join.

  set (inner_join :=
    ((fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert kx (Bin s k l1 l2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin s k l1 l2) r
                   then
                    if isBalanced r (Bin s k l1 l2)
                    then bin kx (Bin s k l1 l2) r
                    else balanceL k l1 (join kx l2 r)
                   else balanceR z (join_inner lz) rz
                end) r1)) in *.

  intro vrec_ij.
  intro sij.
  unfold size in sij.
  fold size in sij.

  unfold balanceR.
  case_eq (isBalanced r2 inner_join).

  intro bbal.
  unfold isBalanced in bbal.
  unfold isBalancedSizeZ in bbal.
  apply Zle_bool_imp_le in bbal.
  rewrite H2 in *.
  rewrite H11 in *.
  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold Size in *.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  intro uunb.
  unfold isBalanced in uunb.
  unfold isBalancedSizeZ in uunb.
  rewrite H2 in *.
  rewrite H11 in *.

  case (Z_gt_le_dec (1 * (size inner_join + 1)) (3 * (size r2 + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite uunb in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear uunb.
  intro uunb.

  unfold rotateR.

  destruct inner_join.
  apply False_ind.
  clear - uunb r2nneg.
  unfold size in uunb.
  fold size in uunb.
  psatzl Z.

  assert (0 <= size inner_join1) as ij10.
  apply size_nnegZ.
  eauto.
  assert (0 <= size inner_join2) as ij20.
  apply size_nnegZ.
  eauto.

  assert (s1 = size inner_join1 + size inner_join2 + 1) as s1_eq.
  assert (validsize (Bin s1 k1 inner_join1 inner_join2)).
  eauto.
  unfold validsize in H10.
  unfold size in H10.
  rewrite <- H10.
  clear H10.
  unfold realsize.
  fold realsize.
  replace (size inner_join1) with (realsize inner_join1).
  replace (size inner_join2) with (realsize inner_join2).
  unfold Size in *.
  psatzl Z.
  assert (validsize inner_join2); eauto.
  assert (validsize inner_join1); eauto.

  unfold size in sij.
  fold size in sij.
  unfold size in uunb.
  fold size in uunb.

  unfold balanced in IHr1.
  fold balanced in IHr1.
  unfold isBalanced in IHr1.
  unfold isBalancedSizeZ in IHr1.
  rewrite H2 in *.
  rewrite H11 in *.
  apply andb_prop_elim in IHr1.
  destruct IHr1.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  apply Is_true_eq_true in H10.
  apply Is_true_eq_true in H16.
  apply Zle_bool_imp_le in H10.
  apply Zle_bool_imp_le in H16.

  case_eq (isSingle inner_join2 inner_join1).
  intro iii.
  unfold isSingle in iii.
  unfold isSingleSizeP in iii.
  rewrite H12 in iii.
  rewrite H13 in iii.
  eapply Zgt_is_gt_bool in iii.
  unfold singleR.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold size.
  fold size.
  unfold Size in *.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  auto.
  auto.

  intro double.
  unfold isSingle in double.
  unfold isSingleSizeP in double.

  case (Z_gt_le_dec (ratioU * (size inner_join1 + 1))
             (ratioD * (size inner_join2 + 1))).
  intro gt.
  eapply Zgt_is_gt_bool in gt.
  rewrite gt in double.
  apply False_ind.
  discriminate.
  clear double.
  intro double.
  rewrite H12 in *.
  rewrite H13 in *.

  unfold doubleR.
  case_eq inner_join2.
  intro tip.
  rewrite tip in *.
  clear inner_join2 tip.
  unfold size in double.
  fold size in double.
  apply False_ind.
  psatzl Z.

  intros s2 k2 f f0.
  intro ijbin.
  assert (validsize_rec (Bin s2 k2 f f0)).
  rewrite <- ijbin.
  eauto.
  assert (s2 = size f + size f0 + 1) as s2_eq.
  assert (validsize (Bin s2 k2 f f0)).
  eauto.
  unfold validsize in H18.
  unfold realsize in H18.
  fold realsize in H18.
  unfold size in H18.
  rewrite <- H18.
  clear H18.
  replace (size f) with (realsize f).
  replace (size f0) with (realsize f0).
  unfold Size in *.
  psatzl Z.
  assert (validsize f0); eauto.
  assert (validsize f); eauto.

  rewrite ijbin in *.
  clear ijbin inner_join2.
  unfold size in ij20.

  assert (0 <= size f).
  apply size_nnegZ.
  eauto.
  assert (0 <= size f0).
  apply size_nnegZ.
  eauto.

  unfold size in H10.
  fold size in H10.

  unfold balanced in H14.
  fold balanced in H14.
  apply andb_prop_elim in H14.
  destruct H14.
  apply andb_prop_elim in H14.
  destruct H14.
  apply andb_prop_elim in H14.
  destruct H14.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite H2 in *.
  rewrite H11 in *.
  apply Is_true_eq_true in H14.
  apply Is_true_eq_true in H22.
  apply Zle_bool_imp_le in H14.
  apply Zle_bool_imp_le in H22.
  unfold size in s1_eq.
  fold size in s1_eq.
  unfold size in double.
  fold size in double.

  unfold size in H16.
  fold size in H16.

  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.

  unfold size.
  fold size.
  unfold Size in *.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  apply good32.
  unfold p32.
  intuition.
  eauto.
  eauto.
  Qed.


(*
   now we are going to reason about set operations on
   delta = 3 and ratio = 2
*)
Lemma merge_size:
  p32 ->
  forall (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (merge_ l r) /\
      (size (merge_ l r) = size l + size r) /\
      Is_true (balanced (merge_ l r))
    ) .
  intro gp.
  intros l r.
  generalize r.
  clear r.
  induction l.

  (* left is Tip *)
  induction r.
  intros triv triv2.
  clear triv triv2.
  intros triv triv2.
  clear triv triv2.
  split.
  compute.
  reflexivity.
  compute.
  split.
  reflexivity.
  trivial.

  (* left is Tip, right is Bin *)
  intro triv.
  intro vrec.
  intro balt.
  intro balr.
  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.
  
  destruct IHr1.
  eauto.
  eauto.
  eauto.
  eauto.

  destruct IHr2.
  eauto.
  eauto.
  eauto.
  eauto.

  unfold merge_ in *.
  split.
  eauto.
  unfold size.
  unfold Size in *.
  split.
  psatzl Z.
  unfold balanced.
  repeat (apply andb_prop_intro; split); assumption.

  (* left is Bin *)
  induction r.
  intro vrecl.
  intro triv.
  clear triv.
  intro bl.
  intro triv.
  clear triv.

  unfold merge_.
  split.
  auto.
  split.
  unfold size.
  unfold Size in *.
  psatzl Z.
  auto.

  intro vrecl.
  intro vrecr.
  intro ball.
  intro balr.
  destruct IHr1.
  auto.
  eauto.
  auto.
  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H.
  destruct H.
  auto.

  (* Both are Bin *)
  destruct IHr2.
  eauto.
  eauto.
  auto.
  unfold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H1.
  destruct H1.
  auto.
  assert (Is_true (balanced (Bin s k l1 l2))).
  auto.
  unfold balanced in H3.
  fold balanced in H3.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.

  assert (Is_true (balanced (Bin s0 k0 r1 r2))) as balr_backup.
  assumption.
  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr as [balr balr2].
  apply andb_prop_elim in balr.
  destruct balr as [balr balr1].
  apply andb_prop_elim in balr.
  destruct balr as [isbalr12 isbalr21].

  assert (s = size l1 + size l2 + 1).
  rename H3 into H33.
  assert (validsize (Bin s k l1 l2)) as H3.
  eauto.
  unfold validsize in H3.
  unfold size in H3.
  rewrite <- H3.
  clear H3.
  unfold realsize.
  fold realsize.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  unfold Size in *.
  psatzl Z.

  assert (validsize l2); eauto.
  assert (validsize l1); eauto.

  assert (s0 = size r1 + size r2 + 1).
  rename H4 into H44.
  assert (validsize (Bin s0 k0 r1 r2)) as H4.
  eauto.
  unfold validsize in H4.
  unfold size in H4.
  rewrite <- H4.
  unfold realsize.
  fold realsize.
  replace (size r1) with (realsize r1).
  replace (size r2) with (realsize r2).
  unfold Size in *.
  psatzl Z.
  assert (validsize r2); eauto.
  assert (validsize r1); eauto.

  unfold merge_ in *.
  fold merge_.
  fold merge_ in H1.
  fold merge_ in H2.
  fold merge_ in H0.
  fold merge_ in H.
  fold merge_ in IHl2.
  fold merge_ in IHl1.

  set (inner :=
            ((fix merge_inner (y : FSet) : FSet :=
            match y with
            | Tip => Bin s k l1 l2
            | Bin _ ky ly ry =>
                if isBalanced (Bin s k l1 l2) y
                then
                 if isBalanced y (Bin s k l1 l2)
                 then glue (Bin s k l1 l2) y
                 else balanceL ky ly (merge_ l2 y)
                else balanceR ky (merge_inner ly) ry
            end))) in *.
  unfold size in H0.
  fold size in H0.
  unfold size in H2.
  fold size in H2.

  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  unfold p32 in gp.
  destruct gp as [gp0 gp1].
  destruct gp1 as [gp1 gp2].
  destruct gp2 as [gp2 gp3].
  rewrite gp0 in *.
  rewrite gp1 in *.

  apply Is_true_eq_true in H3.
  apply Is_true_eq_true in H6.
  apply Zle_bool_imp_le in H3.
  apply Zle_bool_imp_le in H6.
  apply Is_true_eq_true in isbalr12.
  apply Is_true_eq_true in isbalr21.
  apply Zle_bool_imp_le in isbalr12.
  apply Zle_bool_imp_le in isbalr21.

  assert (0 <= size l1) as l1nneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size l2) as l2nneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size r1) as r1nneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size r2) as r2nneg.
  apply size_nnegZ.
  eauto.

  case_eq (
    Zle_bool (1 * (size (Bin s0 k0 r1 r2) + 1))
           (3 * (size (Bin s k l1 l2) + 1))).
  intro bal.
  apply Zle_bool_imp_le in bal.
  unfold size in bal.

  case_eq (
    Zle_bool (1 * (size (Bin s k l1 l2) + 1))
           (3 * (size (Bin s0 k0 r1 r2) + 1))).
  intro bbal.
  apply Zle_bool_imp_le in bbal.
  eauto.
  unfold size in bbal.

  generalize glue_decr.
  intro gd.
  destruct gd with (Bin s k l1 l2) (Bin s0 k0 r1 r2).

  apply good32.
  unfold p32.
  intuition.
  eauto.
  eauto.
  eauto.
  assumption.

  apply Is_true_eq_left.
  unfold isBalanced.
  unfold size.
  unfold isBalancedSizeZ.
  apply Zle_imp_le_bool.
  rewrite gp0.
  rewrite gp1.
  assumption.

  apply Is_true_eq_left.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  unfold size.
  rewrite gp0.
  rewrite gp1.
  apply Zle_imp_le_bool.
  assumption.

  clear gd.
  intuition.

  intro ubal.
  case (Z_gt_le_dec
    (1 * (size (Bin s k l1 l2) + 1))
           (3 * (size (Bin s0 k0 r1 r2) + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite ubal in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear ubal.
  intro ubal.
  unfold size in ubal.

  split.
  eapply validsize_balanceL.
  eauto.

  eapply IHl2.
  eauto.
  eauto.
  eauto.
  eauto.

  clear inner.
  set (inner :=
                ((fix merge_inner (y : FSet) : FSet :=
                match y with
                | Tip => Bin s k l1 l2
                | Bin _ ky ly ry =>
                    if Zle_bool (1 * (size y + 1))
                         (3 * (size (Bin s k l1 l2) + 1))
                    then
                     if Zle_bool (1 * (size (Bin s k l1 l2) + 1))
                          (3 * (size y + 1))
                     then glue (Bin s k l1 l2) y
                     else balanceL ky l1 (merge_ l2 y)
                    else balanceR ky (merge_inner ly) ry
                end)))
   in *.
  
  split.
  destruct IHl2 with (Bin s0 k0 r1 r2).
  eauto.
  eauto.
  auto.
  eauto.

  rewrite size_balanceLZ.
  destruct H10.
  rewrite H10.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  eauto.
  auto.

  destruct IHl2 with (Bin s0 k0 r1 r2).
  eauto.
  eauto.
  eauto.
  eauto.
  destruct H10.

  unfold balanceL.
  case_eq (isBalanced l1 (merge_ l2 (Bin s0 k0 r1 r2))).
  intro bbal.
  unfold isBalanced in bbal.
  rewrite H10 in bbal.
  unfold size in bbal.
  fold size in bbal.
  unfold isBalancedSizeZ in bbal.
  apply Zle_bool_imp_le in bbal.
  rewrite gp0 in bbal.
  rewrite gp1 in bbal.

  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  rewrite H10.
  unfold size.
  fold size.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  eauto.
  eauto.
  intro unbal.
  unfold isBalanced in unbal.
  rewrite H10 in unbal.
  unfold size in unbal.
  fold size in unbal.
  unfold isBalancedSizeZ in unbal.

  case (Z_gt_le_dec
    (deltaD * (size l2 + s0 + 1)) (deltaU * (size l1 + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unbal in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear unbal.
  rewrite gp0.
  rewrite gp1.
  intro unbal.

  unfold size in H10.
  fold size in H10.

  unfold rotateL.

  case_eq (merge_ l2 (Bin s0 k0 r1 r2)).
  intro tip.
  rewrite tip in H10.
  apply False_ind.
  unfold size in H10.
  fold size in H10.
  unfold Size in *.
  psatzl Z.

  intros s1 k1 f f0.
  intro mbin.
  rewrite mbin in *.

  assert (s1 = size f + size f0 + 1) as s1_eq.
  assert (validsize (Bin s1 k1 f f0)).
  eauto.
  unfold validsize in H12.
  unfold size in H12.
  rewrite <- H12.
  unfold realsize.
  fold realsize.
  replace (size f) with (realsize f).
  replace (size f0) with (realsize f0).
  unfold Size in *.
  psatzl Z.
  assert (validsize f0); eauto.
  assert (validsize f); eauto.

  unfold size in H10.
  fold size in H10.

  assert (0 <= size f) as fnneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size f0) as f0nneg.
  apply size_nnegZ.
  eauto.

  case_eq (isSingle f f0).
  unfold isSingle.
  unfold isSingleSizeP.
  rewrite gp2.
  rewrite gp3.
  intro single.
  eapply Zgt_is_gt_bool in single.

  unfold singleL.
  unfold bin.
  unfold size; fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  unfold size; fold size.
  unfold Size in *.

  unfold balanced in H11.
  fold balanced in H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite gp0 in *.
  rewrite gp1 in *.
  apply Is_true_eq_true in H11.
  apply Is_true_eq_true in H14.
  apply Zle_bool_imp_le in H11.
  apply Zle_bool_imp_le in H14.
  
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  auto.

  intro double.
  unfold isSingle in double.
  unfold isSingleSizeP in double.
  rewrite gp2 in *.
  rewrite gp3 in *.
  case (Z_gt_le_dec (2 * (size f0 + 1)) (1 * (size f + 1))).
  intro gt.
  eapply Zgt_is_gt_bool in gt.
  rewrite double in gt.
  apply False_ind.
  discriminate.

  clear double.
  intro double.

  unfold doubleL.
  destruct f.

  unfold size in double.
  fold size in double.
  apply False_ind.
  psatzl Z.
  
  assert (s2 = size f1 + size f2 + 1) as s2_eq.
  assert (validsize (Bin s2 k2 f1 f2)).
  eauto.
  unfold validsize in H12.
  unfold size in H12.
  rewrite <- H12.
  clear H12.
  unfold realsize.
  fold realsize.
  replace (size f1) with (realsize f1).
  replace (size f2) with (realsize f2).
  unfold Size in *.
  psatzl Z.
  assert (validsize f2); eauto.
  assert (validsize f1); eauto.

  unfold size in double.
  fold size in double.
  unfold size in fnneg.
  unfold size in s1_eq.
  fold size in s1_eq.
  unfold balanced in H11.
  fold balanced in H11.
  unfold isBalanced in H11.
  unfold isBalancedSizeZ in H11.
  rewrite gp0 in *.
  rewrite gp1 in *.
  unfold size in H11.
  fold size in H11.

  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H13.
  destruct H13.
  apply andb_prop_elim in H13.
  destruct H13.
  apply andb_prop_elim in H13.
  destruct H13.

  apply Is_true_eq_true in H11.
  apply Is_true_eq_true in H14.
  apply Is_true_eq_true in H13.
  apply Is_true_eq_true in H17.
  apply Zle_bool_imp_le in H11.
  apply Zle_bool_imp_le in H13.
  apply Zle_bool_imp_le in H14.
  apply Zle_bool_imp_le in H17.

  assert (0 <= size f1).
  apply size_nnegZ.
  eauto.

  assert (0 <= size f2).
  apply size_nnegZ.
  eauto.

  unfold balanced.
  unfold bin.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  unfold size.
  fold size.
  rewrite gp0.
  rewrite gp1.
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  rewrite s1_eq in *.
  clear s1 s1_eq.
  rewrite s2_eq in *.
  clear s2 s2_eq.
  rewrite H7 in *.
  rewrite H8 in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.
  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.
  auto.

  intro unb.
  clear inner.
  set (inner :=
    fix merge_inner (y : FSet) : FSet :=
            match y with
            | Tip => Bin s k l1 l2
            | Bin _ ky ly ry =>
                if Zle_bool (1 * (size y + 1))
                     (3 * (size (Bin s k l1 l2) + 1))
                then
                 if Zle_bool (1 * (size (Bin s k l1 l2) + 1))
                      (3 * (size y + 1))
                 then glue (Bin s k l1 l2) y
                 else balanceL ky l1 (merge_ l2 y)
                else balanceR ky (merge_inner ly) ry
            end) in *.
  case (Z_gt_le_dec
    (1 * (size (Bin s0 k0 r1 r2) + 1))
          (3 * (size (Bin s k l1 l2) + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear unb.
  intro unb.
  unfold size in unb.
  unfold balanceR.
  case_eq (isBalanced r2 (inner r1)).
  intro bal.
  split.
  apply validsize_rec_bin.
  auto.
  eauto.
  
  generalize bal.
  clear bal.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  intro bal.
  apply Zle_bool_imp_le in bal.
  split.
  unfold Size in *.
  psatzl Z.

  unfold Size in *.
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  intuition.
  intuition.

  intro unbal.
  split.
  apply validsize_rec_rotateR.
  auto.
  eauto.

  unfold isBalanced in unbal.
  unfold isBalancedSizeZ in unbal.

  case (Z_le_gt_dec (deltaD * (size (inner r1) + 1)) (deltaU * (size r2 + 1))).
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unbal in le.
  apply False_ind.
  discriminate.

  clear unbal.
  intro unbal.
  rewrite gp0 in *.
  rewrite gp1 in *.

  unfold rotateR.
  destruct (inner r1).
  apply False_ind.
  unfold size in unbal.
  fold size in unbal.
  psatzl Z.

  destruct H0.
  unfold size in H0.
  fold size in H0.
  move H9 at bottom.
  unfold balanced in H9.
  fold balanced in H9.
  apply andb_prop_elim in H9.
  destruct H9.
  apply andb_prop_elim in H9.
  destruct H9.
  apply andb_prop_elim in H9.
  destruct H9.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  apply Is_true_eq_true in H9.
  apply Is_true_eq_true in H12.
  apply Zle_bool_imp_le in H9.
  apply Zle_bool_imp_le in H12.

  rewrite gp0 in *.
  rewrite gp1 in *.
  
  assert (s1 = size f1 + size f2 + 1).
  assert (validsize (Bin s1 k1 f1 f2)).
  eauto.
  unfold validsize in H13.
  unfold size in H13.
  rewrite <- H13.
  unfold realsize.
  fold realsize.
  replace (size f1) with (realsize f1).
  replace (size f2) with (realsize f2).
  unfold Size in *.
  psatzl Z.

  assert (validsize f2); eauto.
  assert (validsize f1); eauto.

  unfold isSingle.
  unfold isSingleSizeP.
  rewrite gp2.
  rewrite gp3.

  assert (0<= size f1).
  apply size_nnegZ.
  eauto.

  assert (0 <= size f2).
  apply size_nnegZ.
  eauto.
  
  unfold size in unbal.
  fold size in unbal.

  case_eq (Zgt_bool (2 * (size f1 + 1)) (1 * (size f2 + 1))).
  intro single.
  eapply Zgt_is_gt_bool in single.
  unfold singleR.
  unfold bin.
  unfold size.
  fold size.


  unfold Size in *.

  split.
  psatzl Z.

  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  unfold size.
  fold size.
  rewrite gp0.
  rewrite gp1.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.
  auto.

  intro double.
  case (Z_gt_le_dec
    (2 * (size f1 + 1)) (1 * (size f2 + 1))).
  intro gt.
  eapply Zgt_is_gt_bool in gt.
  rewrite double in gt.
  apply False_ind.
  discriminate.
  clear double.
  intro double.

  unfold doubleR.

  destruct f2.
  apply False_ind.
  unfold size in double.
  fold size in double.
  psatzl Z.

  unfold size in double.
  fold size in double.
  unfold size in H15.
  unfold size in H13.
  fold size in H13.
  unfold size in H12.
  fold size in H12.
  unfold size in H9.
  fold size in H9.
  
  (* s2 = *)
  assert (s2 = size f2_1 + size f2_2 + 1).
  assert (validsize (Bin s2 k2 f2_1 f2_2)).
  eauto.
  unfold validsize in H16.
  unfold size in H16.
  rewrite <- H16.
  unfold realsize.
  fold realsize.
  replace (size f2_1) with (realsize f2_1).
  replace (size f2_2) with (realsize f2_2).
  unfold Size in *.
  psatzl Z.

  assert (validsize f2_2); eauto.
  assert (validsize f2_1); eauto.

  (* 0<= *)
  assert (0 <= size f2_1).
  apply size_nnegZ.
  eauto.

  assert (0 <= size f2_2).
  apply size_nnegZ.
  eauto.

  (* f2_1 f2_2 balance *)
  unfold balanced in H10.
  fold balanced in H10.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite gp0 in *.
  rewrite gp1 in *.
  apply Is_true_eq_true in H10.
  apply Is_true_eq_true in H21.
  apply Zle_bool_imp_le in H10.
  apply Zle_bool_imp_le in H21.
  
  unfold bin.
  unfold size.
  fold size.
  unfold Size in *.
  split.
  psatzl Z.

  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  unfold size.
  fold size.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  Qed.

Inductive Ordering := LT' | GT' | EQ'.

Fixpoint filterGt (cmp: K -> Ordering) (t: FSet): FSet :=
  match t with
    | Tip => Tip
    | Bin _ kx l r =>
      match cmp kx with
        | LT' => join kx (filterGt cmp l) r
        | GT' => filterGt cmp r
        | EQ' => r
      end
  end.

Fixpoint filterLt (cmp: K -> Ordering) (t: FSet): FSet :=
  match t with
    | Tip => Tip
    | Bin _ kx l r =>
      match cmp kx with
        | LT' => filterLt cmp l
        | GT' => join kx l (filterLt cmp r)
        | EQ' => l
      end
  end.

Fixpoint trim (cmplo cmphi: K -> Ordering) (t: FSet) : FSet :=
  match t with
    | Tip => Tip
    | Bin _ kx l r =>
      match cmplo kx with
        | LT' => match cmphi kx with
                  | GT' => t
                  | _  => trim cmplo cmphi l
                end
        | _ => trim cmplo cmphi r
      end
  end.

Definition COconv: forall (x y: X.t), (Compare X.lt X.eq x y) -> Ordering.
intros x y.
intro comp.
destruct comp.
exact LT'.
exact EQ'.
exact GT'.
Defined.

Fixpoint hedgeUnionL (cmplo cmphi: K -> Ordering)
  (t1 t2: FSet) := 
  match t2 with
    | Tip => t1
    | Bin _ kx l r =>
      match t1 with
        | Tip => join kx (filterGt cmplo l) (filterLt cmphi r)
        | Bin _ kx l r =>
          let cmpkx k := COconv kx k (X.compare kx k) in
          join kx (hedgeUnionL cmplo cmpkx l (trim cmplo cmpkx t2)) 
              (hedgeUnionL cmpkx cmphi r (trim cmpkx cmphi t2))
      end
  end.

  
Definition union (t1 t2: FSet) :=
  match t1 with
    | Tip => t2
    | _ =>
      match t2 with
        | Tip => t1
        | _ =>
          hedgeUnionL (fun x => LT') (fun x => GT') t1 t2
      end
  end.

Lemma filterGt_vrec:
  good_params ->
  forall (cmplo : K -> Ordering) (r1: FSet),
    validsize_rec r1 ->
    validsize_rec (filterGt cmplo r1).
  intro gp.
  intros cmplo r.
  induction r.
  compute.
  reflexivity.

  unfold filterGt.
  fold filterGt.
  intro ih.
  case (cmplo k).
  eapply join_size.
  assumption.
  apply IHr1.
  eauto.
  eauto.
  apply IHr2.
  eauto.
  eauto.
  Qed.


Lemma filterLt_vrec:
  good_params ->
  forall (cmplo : K -> Ordering) (r1: FSet),
    validsize_rec r1 ->
    validsize_rec (filterLt cmplo r1).
  intro gp.
  intro cmplo.
  induction r1.
  compute.
  auto.
  intro ih.
  unfold filterLt.
  fold filterLt.
  case (cmplo k).
  apply IHr1_1.
  eauto.
  eapply join_size.
  assumption.
  eauto.
  apply IHr1_2.
  eauto.
  eauto.
  Qed.

Lemma filterGt_balanced:
  p32 ->
  forall (cmplo: K->Ordering) (r1: FSet),
    validsize_rec r1 ->
    Is_true (balanced r1) ->
    Is_true (balanced (filterGt cmplo r1)).
  intro p.
  intros cmplo r.
  induction r.
  compute.
  auto.
  unfold filterGt.
  fold filterGt.
  intro vrecbin.
  intro balbin.
  unfold balanced in balbin.
  fold balanced in balbin.
  apply andb_prop_elim in balbin.
  destruct balbin.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.
  assert (Is_true (balanced (filterGt cmplo r1))).
  apply IHr1.
  eauto.
  auto.
  clear IHr1.

  assert (Is_true (balanced (filterGt cmplo r2))).
  apply IHr2.
  eauto.
  auto.
  
  case (cmplo k).
  apply join_balanced.
  assumption.
  auto.
  apply filterGt_vrec.
  apply good32.
  assumption.
  eauto.
  auto.
  eauto.
  auto.
  auto.
  Qed.
  

Lemma filterLt_balanced:
  p32 ->
  forall (cmplo: K->Ordering) (r1: FSet),
    validsize_rec r1 ->
    Is_true (balanced r1) ->
    Is_true (balanced (filterLt cmplo r1)).
  intro p.
  intros cmplo l.
  induction l.
  intro vall.
  intro ball.
  compute.
  trivial.

  intros vrec bal.
  unfold balanced in bal
    .
  fold balanced in bal.
  apply andb_prop_elim in bal.
  destruct bal.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.

  assert (Is_true (balanced (filterLt cmplo l1))).
  apply IHl1.
  eauto.
  eauto.
  assert (Is_true (balanced (filterLt cmplo l2))).
  apply IHl2.
  eauto.
  auto.

  unfold filterLt.
  fold filterLt.
  case (cmplo k).
  auto.
  eapply join_balanced.
  assumption.
  auto.
  eauto.
  auto.
  apply filterLt_vrec.
  apply good32.
  assumption.
  eauto.
  auto.
  Qed.


Lemma valsize_trim:
  forall (cmplo cmphi: K->Ordering) (t: FSet),
    validsize_rec t ->
    validsize_rec
     (trim cmplo cmphi t).
  intros cmplo cmphi t.
  induction t.
  compute.
  reflexivity.
  unfold trim.
  fold trim.
  case (cmplo k); eauto.
  case (cmphi k); eauto.
  Qed.

Lemma balanced_trim:
  forall (cmplo cmphi: K->Ordering) (t: FSet),
    validsize_rec t ->
    Is_true (balanced t) ->
    Is_true (balanced
     (trim cmplo cmphi t)).
  intros cmplo cmphi t.
  induction t.
  eauto.
  intros.

  unfold balanced in H0.
  fold balanced  in H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.

  assert (Is_true (balanced (trim cmplo cmphi t1))).
  apply IHt1.
  eauto.
  eauto.
  clear IHt1.

  assert (Is_true (balanced (trim cmplo cmphi t2))).
  apply IHt2.
  eauto.
  auto.
  
  unfold trim.
  fold trim.
  case (cmplo k); eauto.
  case (cmphi k); eauto.
  auto.
  unfold balanced.
  repeat (apply andb_prop_intro; split); eauto.
  Qed.

Lemma hedgeunion_balance:
  p32 ->
  forall (cmplo cmphi: K->Ordering) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (hedgeUnionL cmplo cmphi l r) /\
      Is_true (balanced (hedgeUnionL cmplo cmphi l r))
    ) .
  intro p.
  intros cmplo cmphi l.
  generalize cmplo cmphi.
  clear cmplo cmphi.
  induction l.
  intros cmplo cmphi.
  induction r.
  intros.
  unfold hedgeUnionL.
  intuition.

  intros.

  unfold balanced in H2.
  fold balanced in H2.
  repeat (apply andb_prop_elim in H2;   destruct H2).
  
  destruct IHr1.
  eauto.
  eauto.
  eauto.
  auto.

  destruct IHr2; eauto.

  unfold hedgeUnionL.
  split.
  eapply join_size.
  apply good32.
  assumption.

  apply filterGt_vrec.
  apply good32.
  assumption.
  eauto.

  apply filterLt_vrec.
  apply good32.
  assumption.
  eauto.

  generalize join_size.
  intro js.
  destruct js with k (filterGt cmplo r1) (filterLt cmphi r2).
  apply good32.
  assumption.

  apply filterGt_vrec.
  apply good32; assumption.
  eauto.

  apply filterLt_vrec.
  apply good32; assumption.
  eauto.

  clear js.

  apply join_balanced.
  assumption.

  apply filterGt_balanced.
  assumption.
  eauto.
  auto.

  apply filterGt_vrec.
  apply good32.
  assumption.
  eauto.
  apply filterLt_balanced.
  assumption.
  eauto.
  auto.

  apply filterLt_vrec.
  apply good32.
  assumption.
  eauto.

  (* left is bin *)
  intros cmplo cmphi.
  intro r.
  unfold hedgeUnionL in *.
  fold hedgeUnionL.
  fold hedgeUnionL in IHl2.
  fold hedgeUnionL in IHl1.

  intro vrecbin.
  intro vrecr.
  intro bal.
  unfold balanced in bal.
  fold balanced in bal.

  apply andb_prop_elim in bal.
  destruct bal.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.
  intro balr.
  destruct r.
  split.
  auto.
  unfold balanced.
  fold balanced.
  apply Is_true_eq_true in H.
  apply Is_true_eq_true in H2.
  apply Is_true_eq_true in H1.
  apply Is_true_eq_true in H0.
  rewrite H.
  rewrite H2.
  rewrite H1.
  rewrite H0.
  compute.
  trivial.

  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.

  split.
  eapply join_size.
  apply good32.
  assumption.

  eapply IHl1.
  eauto.

  apply valsize_trim.
  eauto.
  eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro; split; auto).

  eapply IHl2; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro; split; auto).

  apply join_balanced; auto.
  eapply IHl1; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro ; split; auto).

  eapply IHl1; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro; split; auto).

  eapply IHl2; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  repeat (apply andb_prop_intro; split; auto).

  eapply IHl2; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  repeat (apply andb_prop_intro; split; auto).
  Qed.


(* union operation keeps balance *)

Lemma union_balanced:
  p32 ->
  forall (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (union l r) /\
      Is_true (balanced (union l r))
    ) .
  intro p.
  intros l r.
  intros.
  unfold union.

  destruct l.
  intuition.
  destruct r.
  intuition.

  eapply hedgeunion_balance; eauto.

  Qed.


Fixpoint hedgeDiff (cmplo cmphi: K->Ordering) (t t2: FSet) :=
  match t with
    | Tip => Tip
    | Bin _ kx l r =>
      match t2 with
        | Tip => join kx (filterGt cmplo l) (filterLt cmphi r)
        | Bin _ kx l r =>
          let cmpkx k := COconv kx k (X.compare kx k) in
          merge_ (hedgeDiff cmplo cmpkx (trim cmplo cmpkx t) l) 
          (hedgeDiff cmpkx cmphi (trim cmpkx cmphi t) r)
      end
  end.


Lemma hedgediff_balance:
  p32 ->
  forall (cmplo cmphi: K->Ordering) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (hedgeDiff cmplo cmphi l r) /\
      Is_true (balanced (hedgeDiff cmplo cmphi l r))
    ) .
  intro p.
  intros cmplo cmphi l r.
  generalize l.
  clear l.
  generalize cmplo cmphi.
  clear cmplo cmphi.
  induction r.
  intros cmplo cmphi l.
  intros vrecl vrect ball balt.
  unfold hedgeDiff.
  destruct l.
  compute.
  auto.

  assert ( Is_true (balanced (Bin s k l1 l2))) as ball_bkp.
  assumption.
  unfold balanced in ball.
  fold balanced in ball.
  apply andb_prop_elim in ball.
  destruct ball.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.

  split.
  eapply join_size; eauto.
  apply good32; auto.
  apply filterGt_vrec.
  apply good32; auto.
  eauto.
  apply filterLt_vrec.
  apply good32; auto.
  eauto.
  apply join_balanced; eauto.
  apply filterGt_balanced; eauto.
  apply filterGt_vrec; eauto.
  apply good32; assumption.
  apply filterLt_balanced; eauto.
  apply filterLt_vrec; eauto.
  apply good32 ;assumption.

  intros cmplo cmphi l.
  intro vrecl.
  intro vrecr.
  intro ball.
  intro balr.
  assert (Is_true (balanced (Bin s k r1 r2))) as balr_bkp.
  assumption.

  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.

  unfold hedgeDiff.
  fold hedgeDiff.

  destruct l.
  intuition.

  generalize merge_size.
  intro ms.
  destruct ms with
            (hedgeDiff cmplo (fun k1 : X.t => COconv k k1 (X.compare k k1))
              (trim cmplo (fun k1 : X.t => COconv k k1 (X.compare k k1))
                (Bin s0 k0 l1 l2)) r1)
            (hedgeDiff (fun k1 : X.t => COconv k k1 (X.compare k k1)) cmphi
              (trim (fun k1 : X.t => COconv k k1 (X.compare k k1)) cmphi
                (Bin s0 k0 l1 l2)) r2).
  assumption.
  clear ms.
  eapply IHr1.
  apply valsize_trim; eauto.
  eauto.
  apply balanced_trim; eauto.
  eauto.

  eapply IHr2.
  apply valsize_trim; eauto.
  eauto.
  apply balanced_trim; eauto.
  eauto.

  eapply IHr1.
  apply valsize_trim.
  eauto.
  eauto.

  apply balanced_trim; eauto.
  eauto.

  eapply IHr2; eauto.
  apply valsize_trim; eauto.

  eapply balanced_trim; eauto.

  intuition.
  Qed.

Definition difference (t1 t2: FSet): FSet :=
  match t1 with
    | Tip => Tip
    | _ =>
      match t2 with
        |  Tip => t1
        | _ => hedgeDiff (fun x => LT') (fun x => GT') t1 t2
      end
  end.

(* difference operation keeps balance *)

Theorem difference_balance:
  p32 ->
  forall (cmplo cmphi: K->Ordering) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (difference  l r) /\
      Is_true (balanced (difference l r))
    ) .
  intro p.
  intros cmplo cmphi.
  intros l r.
  intros vrecl vrecr.
  intros ball balr.
  unfold difference.
  destruct l.
  intuition.
  destruct r.
  eauto.
  apply hedgediff_balance; eauto.
  Qed.

(* splitLookupWithKey *)
Fixpoint splitLookupWithKey (x: K) (t: FSet):
  (FSet * option K * FSet) :=
  match t with
    | Tip => (Tip, None, Tip)
    | Bin _ kx l r =>
      match X.compare x kx with
        | EQ _ =>
          ((l, Some kx), r)
        | LT _ =>
          (let (ltz, gt) := splitLookupWithKey x l in
          let (lt, z) := ltz in
            (lt, z, join kx gt r))
        | GT_  =>
          (let (ltz, gt) := splitLookupWithKey x r in
          let (lt, z) := ltz in 
          (join kx l lt, z, gt))
      end
  end.

(* intersectionwithkey *)
Require Import Recdef.

Open Scope nat_scope.

Fixpoint natsize (t: FSet) :=
  match t with
    | Tip => O
    | Bin _ _ l r =>
      natsize l + natsize r + 1
  end.

Definition sum_natsize (lr: FSet * FSet) :=
  match lr with (l, r) =>
    natsize l + natsize r
  end.

Lemma bin_natsize:
  forall (f1 f2: FSet) (k: K),
   natsize (bin k f1 f2) = natsize f1 + natsize f2 + 1.
  intros f1 f2 k.
  unfold bin.
  unfold natsize.
  fold natsize.
  reflexivity.
  Qed.

Lemma balanceR_natsize:
  forall (f1 f2: FSet) (k: K),
    natsize (balanceR k f1 f2) = natsize f1 + natsize f2 + 1.
  intros.
  unfold balanceR.
  case (isBalanced f2 f1).
  apply bin_natsize.

  unfold rotateR.
  destruct f1.
  unfold assert_false.
  apply bin_natsize.

  case (isSingle f1_2 f1_1).
  unfold singleR.
  rewrite bin_natsize.
  rewrite bin_natsize.
  unfold natsize.
  fold natsize.
  omega.

  unfold doubleR.
  destruct f1_2.
  unfold assert_false.
  rewrite bin_natsize.
  reflexivity.

  rewrite bin_natsize.
  rewrite bin_natsize.
  rewrite bin_natsize.
  unfold natsize.
  fold natsize.
  omega.
  Qed.
  
Lemma balanceL_natsize:
  forall (f1 f2: FSet) (k: K),
    natsize (balanceL k f1 f2) = natsize f1 + natsize f2 + 1.
  intros.
  unfold balanceL.
  case (isBalanced f1 f2).
  rewrite bin_natsize.
  reflexivity.

  unfold rotateL.
  destruct f2.
  unfold assert_false.
  rewrite bin_natsize.
  reflexivity.

  case (isSingle f2_1 f2_2).
  unfold singleL.
  rewrite bin_natsize.
  rewrite bin_natsize.
  unfold natsize.
  fold natsize.
  omega.

  unfold doubleL.
  destruct f2_1.
  unfold assert_false.
  rewrite bin_natsize.
  reflexivity.

  repeat (rewrite bin_natsize).
  unfold natsize. fold natsize.
  omega.
  Qed.


Lemma insert_natsize:
   forall (f : FSet) (x: K),
     natsize (insert x f) <= natsize f + 1.
  induction f.
  unfold insert.
  unfold singleton.
  unfold natsize.
  intuition.

  unfold insert.
  fold insert.
  intro x.
  case (X.compare x k).
  intro l.
  clear l.
  rewrite balanceR_natsize.
  unfold natsize.
  fold natsize.
  assert (natsize (insert x f1) <= natsize f1 + 1).
  eapply IHf1.
  omega.

  intro eq.
  rewrite bin_natsize.
  unfold natsize; fold natsize.
  omega.

  intro lt.
  rewrite balanceL_natsize.
  unfold natsize.
  fold natsize.
  assert (natsize (insert x f2) <= natsize f2 + 1).
  apply IHf2.
  omega.
  Qed.

Lemma join_natsize:
  forall (k: K) (f t2: FSet),
    natsize (join k f t2) <= natsize f + natsize t2 + 1.
  intros k f t2.
  generalize k t2.
  clear k t2.
  induction f.
  unfold join.
  intros x t.
  generalize x.
  clear x.
  induction t.
  unfold insert.
  unfold singleton.
  unfold natsize.
  intro.
  compute.
  intuition.

  intro x.
  generalize (Bin s k t1 t2).
  intro f.
  eapply insert_natsize.

  intros x t.
  generalize x.
  clear x.
  induction t.
  unfold join.
  intro x.
  assert (   natsize (insert x (Bin s k f1 f2)) <=
   natsize (Bin s k f1 f2) + 1
  ).
  apply insert_natsize.
  unfold natsize; fold natsize.
  unfold natsize in H.
  fold natsize in H.
  omega.

  (* Both are bin *)
  unfold join.
  fold join.
  case (isBalanced (Bin s k f1 f2) (Bin s0 k0 t1 t2)).
  case (isBalanced (Bin s0 k0 t1 t2) (Bin s k f1 f2)).
  intro.
  rewrite bin_natsize.
  intuition.

  intro x.
  erewrite balanceL_natsize.
  unfold natsize; fold natsize.
  generalize (IHf2 x (Bin s0 k0 t1 t2)).
  unfold natsize.
  fold natsize.
  omega.

  intro x.
  rewrite balanceR_natsize.
  unfold join in IHt1.
  fold join in IHt1.
  unfold natsize in IHt1; fold natsize in IHt1.
  unfold natsize; fold natsize.
  generalize (IHt1 x).
  set (inner := (fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert x (Bin s k f1 f2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin s k f1 f2) r
                   then
                    if isBalanced r (Bin s k f1 f2)
                    then bin x (Bin s k f1 f2) r
                    else balanceL k f1 (join x f2 r)
                   else balanceR z (join_inner lz) rz
               end)).
  omega.
  Qed.
  


Lemma splitLookupWithKey_right:
  forall (x2: K) (t1 gt_: FSet) (lt_kx: FSet * option K), 
    splitLookupWithKey x2 t1 = (lt_kx, gt_) ->
    natsize gt_ <= natsize t1.
  intros x t.
  generalize x.
  clear x.
  induction t.
  intros x.
  unfold splitLookupWithKey.
  intros.
  simplify_eq H.
  intros.
  rewrite <- H1.
  compute.
  intuition.
  
  intros x r lt_kx.
  unfold splitLookupWithKey.
  fold splitLookupWithKey.
  case (X.compare x k).
  intro lt.
  clear lt.
  intro defs.
  unfold natsize.
  fold natsize.
  assert (r =
    let (ltz, gt) := splitLookupWithKey x t1 in
          join k gt t2).
  generalize defs.
  clear.
  destruct (splitLookupWithKey x t1).
  destruct p.
  intro eq.
  injection eq.
  auto.
  rewrite H.
  case_eq (splitLookupWithKey x t1).
  intros p f.
  intro f_def.
  assert (natsize f <= natsize t1).
  eapply IHt1.
  apply f_def.
  assert (natsize (join k f t2) <= natsize f + natsize t2 + 1).
  apply join_natsize.
  omega.

  intro eq.
  intro d.
  simplify_eq d.
  intros.
  rewrite <- H0.
  unfold natsize.
  fold natsize.
  omega.

  intro lt.
  case_eq (splitLookupWithKey x t2).
  intros p f.
  intro pf.
  destruct p.
  intro lr.
  simplify_eq lr.
  clear lr.
  intros.
  rewrite <- H0.
  clear H0 r.
  assert (natsize f <= natsize t2).
  eapply IHt2.
  apply pf.
  unfold natsize; fold natsize.
  omega.
  Qed.

Lemma splitLookupWithKey_left:
  forall (x2: K) (t1 gt_ lt_: FSet) (kx: option K), 
    splitLookupWithKey x2 t1 = (lt_, kx, gt_) ->
    natsize lt_ <= natsize t1.
  intro x.
  intro t.
  intro r.
  intro l.
  intro y.
  generalize l r y.
  clear l r y.
  induction t.
  unfold splitLookupWithKey.
  intros.
  simplify_eq H.
  intros.
  rewrite <- H0.
  compute.
  intuition.

  unfold splitLookupWithKey.
  fold splitLookupWithKey.
  intros l r y.
  case (X.compare x k).
  intro lt.
  unfold natsize.
  fold natsize.
  case_eq (splitLookupWithKey x t1).
  intros p f.
  destruct p.
  intros.
  assert (natsize l <= natsize t1).
  eapply IHt1.
  simplify_eq H0.
  intros.
  rewrite H1 in H.
  apply H.
  omega.

  intro eq.
  intro d.
  simplify_eq d.
  intros.
  clear d.
  unfold natsize.
  fold natsize.
  rewrite H.
  omega.

  intro lt.
  case_eq (splitLookupWithKey x t2).
  intros.
  destruct p.
  unfold natsize.
  fold natsize.
  simplify_eq H0.
  intros.
  clear H0.
  rewrite <- H1.
  clear H1 l.
  assert (natsize f0 <= natsize t2).
  eapply IHt2.
  apply H.
  generalize (join_natsize k t1 f0).
  intro.
  omega.
  Qed.

Lemma splitLookupBalanced:
  p32 ->
  forall (x2: K) (t1 gt_ lt_: FSet) (kx: option K),
    validsize_rec t1 ->
    Is_true (balanced t1) ->
    splitLookupWithKey x2 t1 = (lt_, kx, gt_) ->
    (validsize_rec lt_ /\
      Is_true (balanced lt_) /\
      validsize_rec gt_ /\
      Is_true (balanced gt_)).
  intro gp.
  intros x t.
  generalize x.
  clear x.
  induction t.
  unfold splitLookupWithKey.
  intros.
  simplify_eq H1.
  intros.
  rewrite <- H2.
  rewrite <- H4.
  intuition.

  unfold splitLookupWithKey.
  fold splitLookupWithKey.
  intros x r l kx.

  case (X.compare x k).
  intro lt.
  case_eq (splitLookupWithKey x t1).
  intros.
  destruct p.
  simplify_eq H2.
  clear H2.
  intros.
  rewrite H2 in *.
  clear H2 f0.
  rewrite H3 in *.
  clear o H3.
  rewrite <- H4 in *.
  clear H4 r.

  clear IHt2.
  generalize (IHt1 x f l kx).
  clear IHt1.
  intros.
  unfold balanced in H1.
  fold balanced in H1.
  apply andb_prop_elim in H1.
  destruct H1.
  apply andb_prop_elim in H1.
  destruct H1.
  
  elim H2.
  clear H2.
  intros.
  destruct H5.
  destruct H6.
  intuition.

  eapply join_size.
  apply good32.
  assumption.
  eauto.
  eauto.
  apply join_balanced.
  assumption.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.

  intro xeq.
  clear xeq.
  intros.
  unfold balanced in H0.
  fold balanced in H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.

  simplify_eq H1.
  clear H1.
  intros.
  rewrite H1 in *.
  clear H1 t1.
  clear kx H5.
  rewrite H6 in *.
  clear t2 H6.
  
  intuition.

  eauto.
  eauto.

  clear IHt1.
  intro xlt.
  clear xlt.
  intros.

  unfold balanced in H0.
  fold balanced in H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.

  case_eq (splitLookupWithKey x t2).
  intros.
  rewrite H5 in H1.
  destruct p.
  simplify_eq H1.
  clear H1.
  intros.
  rewrite <- H1 in *.
  clear l H1.
  rewrite H6 in *.
  clear o H6.
  rewrite H7 in *.
  clear H7 f.

  elim IHt2 with x r f0 kx.
  clear IHt2.
  intros.
  intuition.

  eapply join_size.
  apply good32.
  assumption.
  eauto.
  eauto.

  eapply join_balanced.
  assumption.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  assumption.
  Qed.
  

Function intersectionWithKey (t12: FSet * FSet) {measure sum_natsize t12}:
  FSet :=
  match t12 with (t1, t2) =>
  match t1 with
    | Tip => Tip
    | Bin s1 x1 l1 r1 =>
      match t2 with
        | Tip => Tip
        | Bin s2 x2 l2 r2 =>
          if Z_ge_lt_dec s1 s2 then
            match splitLookupWithKey x2 t1 with (lt_, found, gt_) =>
              let tl := intersectionWithKey (lt_, l2) in
              let tr := intersectionWithKey (gt_, r2) in
                match found with
                  | Some kx => join kx tl tr
                  | None => merge_ tl tr
                end
            end
          else
            match splitLookupWithKey x1 t2 with  (lt_, found, gt_) =>
              let tl := intersectionWithKey (l1, lt_) in
              let tr := intersectionWithKey (r1, gt_) in
                match found with
                  | Some kx => join kx tl tr
                  | None => merge_ tl tr
                end
            end
      end
  end
  end.
intros.
unfold sum_natsize.
rewrite <- teq0 in *.
unfold natsize.
fold natsize.
apply plus_le_lt_compat.
eapply splitLookupWithKey_right.
apply teq3.
omega.
intros.
unfold sum_natsize.
unfold natsize; fold natsize.
generalize (splitLookupWithKey_left x2 (Bin s1 x1 l1 r1) gt_ lt_ (Some kx)).
intro.
apply H in teq3.
unfold natsize in teq3.
fold natsize in teq3.
omega.

intros.
unfold sum_natsize.
unfold natsize.
fold natsize.
generalize (splitLookupWithKey_right x2 (Bin s1 x1 l1 r1) gt_ (lt_, None)).
intro.
apply H in teq3.
clear H.
unfold natsize in teq3.
fold natsize in teq3.
omega.

intros.
unfold sum_natsize.
unfold natsize.
fold natsize.
generalize (splitLookupWithKey_left x2 (Bin s1 x1 l1 r1)).
intro.
apply H in teq3.
unfold natsize in teq3.
fold natsize in teq3.
omega.

intros.
unfold sum_natsize.
unfold natsize.
fold natsize.
generalize (splitLookupWithKey_right x1 (Bin s2 x2 l2 r2) gt_ (lt_, Some kx)).
intro.
apply H in teq3.
unfold natsize in teq3.
fold natsize in teq3.
omega.

intros.
unfold sum_natsize.
unfold natsize.
fold natsize.
generalize (splitLookupWithKey_left x1 (Bin s2 x2 l2 r2)).
intro.
apply H in teq3.
unfold natsize in teq3.
fold natsize in teq3.
omega.

intros.
unfold sum_natsize.
unfold natsize.
fold natsize.
generalize (splitLookupWithKey_right x1 (Bin s2 x2 l2 r2) gt_ (lt_, None)).
intro.
apply H in teq3.
unfold natsize in teq3.
fold natsize in teq3.
omega.

intros.
unfold sum_natsize.
unfold natsize.
fold natsize.
generalize (splitLookupWithKey_left x1 (Bin s2 x2 l2 r2)).
intro.
apply H in teq3.
unfold natsize in teq3.
fold natsize in teq3.
omega.

Qed.

Check intersectionWithKey_ind.

(* some balance condition on intersectionWithKey *)
Definition lrbal (lr: FSet * FSet) (t: FSet) :=
    let (l, r) := lr in
      (validsize_rec l ->
        validsize_rec r ->
        Is_true (balanced l) ->
        Is_true (balanced r) ->
        t = intersectionWithKey (l,r) ->
        ((validsize_rec t) /\
          Is_true (balanced t))).

Lemma intersectionWithKey_balanced:
  p32 ->
  forall (lr: FSet * FSet),
    lrbal lr (intersectionWithKey lr).
  intro p.
  apply intersectionWithKey_ind.

  (* goal 1 *)
  unfold lrbal.
  intros.
  split.
  compute.
  auto.
  compute.
  auto.

  (* goal 2 *)
  intros.
  unfold lrbal.
  intros.
  compute.
  auto.

  (* goal 3 *)
  unfold lrbal.
  intros.
  split.
  eapply join_size.
  apply good32.
  assumption.

  eapply H.
  generalize splitLookupBalanced.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  auto.
  assumption.

  rewrite e0.
  assumption.
  rewrite e0.
  assumption.
  assumption.
  eauto.

  generalize splitLookupBalanced.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  intuition.
  assumption.

  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  reflexivity.

  eapply H0.
  eapply splitLookupBalanced.
  Focus 4.
  eapply e3.
  Unfocus.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  eauto.
  eapply splitLookupBalanced.
  Focus 4.
  apply e3.
  Unfocus.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  reflexivity.

  (* goal 4 *)
  apply join_balanced.
  assumption.
  eapply H.

  generalize splitLookupBalanced.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  auto.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  eauto.

  generalize splitLookupBalanced.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  intuition.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  reflexivity.

  (* goal 4 *)
  eapply H.
  generalize splitLookupBalanced.
  intro si.
  elim si with x2 t1 gt_ lt_ found.
  intros.
  eauto.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.

  intros.
  eauto.
  
  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  auto.

  eapply H0.
  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  reflexivity.

  eapply H0.
  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  reflexivity.

  (* next goal *)
  intros.
  unfold lrbal.
  intros.
  unfold lrbal in H.
  unfold lrbal in H0.
  split.
  eapply merge_size.
  assumption.
  eapply H.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intro.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intro.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  apply andb_prop_elim in  H6.
  intuition.

  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply H.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply merge_size.
  assumption.

  eapply H.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply H.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  (* next goal ... *)
  intros.
  unfold lrbal in *.
  intros.

  split.

  eapply join_size.
  apply good32.
  assumption.

  eapply H.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eauto.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  eapply join_balanced.
  assumption.

  eapply H.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eauto.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  eapply H.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eauto.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  (* last goal!! *)
  intros.
  unfold lrbal in *.

  intros.

  generalize merge_size.
  intro ms.
  elim ms with tl tr.
  clear ms.
  intros.
  intuition.

  clear ms.
  intuition.

  eapply H.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.
  

  eapply H.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.

  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  generalize (splitLookupBalanced p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  Qed.
  

(* define intersection *)
Definition intersection (s1 s2: FSet): FSet :=
  intersectionWithKey (s1, s2).

(* intersection keeps balance *)
Lemma intersection_balance:
  p32 ->
  forall (s1 s2 t: FSet),
      (validsize_rec s1 ->
        validsize_rec s2 ->
        Is_true (balanced s1) ->
        Is_true (balanced s2) ->
        t = intersection s1 s2 ->
        ((validsize_rec t) /\
          Is_true (balanced t))).
  unfold intersection.
  intros.
  generalize intersectionWithKey_balanced.
  intro iwb.
  generalize (iwb H (s1, s2)).
  intro.
  unfold lrbal in H5.
  rewrite H4.
  apply H5; eauto.
Qed.  

Close Scope nat_scope.


(*************************************************
   Part 4: program lemmas.
   union, difference and intersectino keep balance
   under <5/2,3/2>
**************************************************)

Definition p5232 :=
  deltaU = 5 /\ deltaD = 2 /\
  ratioU = 3 /\ ratioD = 2.

Lemma good5232 :
  p5232 -> good_params.
  unfold p5232.
  intuition.
  generalize delta_eq.
  rewrite H0.
  rewrite H.
  intro del.
  generalize ratio_eq.
  rewrite H1.
  rewrite H3.
  intro rat.
  unfold good_params.
  clear H0 H1 H3 H.
  intuition.
  unfold normal.
  split.
  psatzl Q.
  split.
  psatz Q.
  psatzl Q.

  unfold slope.
  psatzl Q.

  unfold curve.
  psatz Q.

  unfold deltasup.
  psatz Q.

  unfold ceilA.
  psatz Q.

  unfold ceilB.

  psatz Q.

  unfold ceilC.
  psatz Q.
  unfold ceilD.
  psatz Q.
  Qed.


Lemma join_balanced5232:
  forall (l r: FSet) (kx: K),
    p5232 ->
    Is_true (balanced l) -> validsize_rec l ->
    Is_true (balanced r) -> validsize_rec r ->
    Is_true (balanced (join kx l r)).
Proof.
  intros l r kx.
  intro p.
  generalize r.
  clear r.
  induction l.

  (* left is Tip *)
  intro r.
  intro baltip.
  clear baltip.
  intro vtip.
  clear vtip.
  induction r.

  (* Tip Tip *)
  intro baltip.
  clear baltip.
  intro vtip.
  clear vtip.
  unfold join.
  apply insert_balanced.
  apply good5232.
  assumption.
  compute.
  auto.
  compute.
  reflexivity.

  (* Tip Bin *)
  intro rbal.
  intro rv.
    (* activate IH *)
    assert (Is_true (balanced r1)).
    eapply NR_S_balanced.
    eauto.
    eapply NR_S_balanced in rbal.
    eauto.
    unfold NRbalanced in rbal.
    intuition.
    apply IHr1 in H.
    unfold join.
    apply insert_balanced.
    apply good5232.
    assumption.
    eauto.
    eauto.
    eauto.

  (* Left is Bin *)
  induction r.

  (* Bin Tip *)
    intro lbal.
    intro lvr.
    intro tbal.
    clear tbal.
    intro vtip.
    clear vtip.
    unfold join.
    apply insert_balanced.
    apply good5232.
    assumption.
    auto.
    auto.

  (* Bin Bin *)
  intro lbal.
  intuition.
  assert (s = size l1 + size l2 + 1) as s_eq.
  assert (validsize (Bin s k l1 l2)).
  eauto.
  unfold validsize in H3.
  unfold realsize in H3.
  fold realsize in H3.
  unfold size in H3.
  rewrite <- H3.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  unfold Size in *.
  psatzl Z.

  assert (validsize l2) ;eauto.
  assert (validsize l1) ;eauto.

  assert (s0 = size r1 + size r2 + 1) as s0_eq.
  assert (validsize (Bin s0 k0 r1 r2)).
  eauto.
  unfold validsize in H3.
  unfold realsize in H3.
  unfold size in H3.
  fold realsize in H3.
  rewrite <- H3.
  replace (size r1) with (realsize r1).
  replace (size r2) with (realsize r2).
  unfold Size in *.
  psatzl Z.

  assert (validsize r2); eauto.
  assert (validsize r1); eauto.

  unfold Size in *.

  assert (0 <= size l1) as l1nneg.
  apply size_nnegZ.
  eauto.

  assert (0 <= size l2) as l2nneg.
  apply size_nnegZ.
  eauto.

  assert (0 <= size r1) as r1nneg.
  apply size_nnegZ.
  eauto.
  
  assert (0 <= size r2) as r2nneg.
  apply size_nnegZ.
  eauto.

  assert (
    Is_true (balanced (join kx (Bin s k l1 l2) r1)) ) as IHr1.
  apply H4.
  eapply NR_S_balanced.
  eapply NR_S_balanced in lbal.
  eauto.
  eauto.
  eapply NR_S_balanced in H0.
  eauto.
  unfold NRbalanced in H0.
  tauto.
  eauto.
  clear H4.

  assert (
    Is_true (balanced (join kx (Bin s k l1 l2) r2)))
  as IHr2.
  apply H2.
  eapply NR_S_balanced.
  eapply NR_S_balanced in H0.
  eauto.
  eauto.
  eapply NR_S_balanced in H0.
  eauto.
  unfold NRbalanced in H0.
  tauto.

  eauto.

  unfold balanced in *.
  fold balanced.
  fold balanced in IHr1.
  fold balanced in IHr2.
  fold balanced in H2.
  fold balanced in H0.
  fold balanced in IHl2.
  fold balanced in IHl1.
  fold balanced in lbal.
  apply andb_prop_elim in H0.
  apply andb_prop_elim in lbal.
  destruct lbal.
  destruct H0.
  apply andb_prop_elim in H3.
  apply andb_prop_elim in H0.
  destruct H0.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H0.
  destruct H0.

  assert (Is_true (balanced r2)).
  assumption.
  apply H2 in H10.
  clear H2.
  Focus 2.
  eauto.
  Unfocus.

  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  apply Is_true_eq_true in H3.
  apply Is_true_eq_true in H8.
  apply Is_true_eq_true in H0.
  apply Is_true_eq_true in H9.

  apply Zle_bool_imp_le in H3.
  apply Zle_bool_imp_le in H8.
  apply Zle_bool_imp_le in H0.
  apply Zle_bool_imp_le in H9.

  unfold p5232 in *.
  destruct p.
  destruct H11.
  destruct H12.
  rewrite H2 in *.
  rewrite H11 in *.
  clear H10.

  unfold join.
  fold join.
  
  case_eq (isBalanced (Bin s k l1 l2) (Bin s0 k0 r1 r2)).
  intro bal.
  case_eq (isBalanced (Bin s0 k0 r1 r2) (Bin s k l1 l2)).
  intro bbal.
  
  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.

  apply Zle_bool_imp_le in bal.
  apply Zle_bool_imp_le in bbal.

  rewrite H2 in *.
  rewrite H11 in *.
  
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  assumption.
  assumption.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  assumption.
  assumption.

  intro unb.
  unfold isBalanced in bal.
  unfold isBalanced in unb.
  unfold isBalancedSizeZ in *.
  apply Zle_bool_imp_le in bal.

  case (Z_gt_le_dec
    (deltaD * (size (Bin s k l1 l2) + 1))
          (deltaU * (size (Bin s0 k0 r1 r2) + 1))).
  intro gt.
  clear unb.

  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.
  Unfocus.

  unfold balanceL.
  case_eq (isBalanced l1 (join kx l2 (Bin s0 k0 r1 r2))).
  intro balt.
  unfold isBalanced in balt.
  unfold isBalancedSizeZ in balt.
  apply Zle_bool_imp_le in balt.

  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.

  rewrite H2 in *.
  rewrite H11 in *.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatz Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  generalize join_size.
  intro js.
  elim js with kx l2 (Bin s0 k0 r1 r2).
  intro vrecj.
  clear js.
  intro sjoin.
  destruct sjoin as [sjoin | sjoin].
  rewrite sjoin.
  
  unfold size.
  fold size.

  psatzl Z.

  rewrite sjoin.
  unfold size; fold size.
  rewrite s_eq in *.
  rewrite s0_eq in *.
  clear s s0 s_eq s0_eq.
  rewrite sjoin in balt.

  unfold size in balt.
  fold size in balt.
  unfold size in gt.
  fold size in gt.
  unfold size in bal.
  fold size in bal.

  psatzl Z.

  apply good5232.
  unfold p5232.
  intuition.

  eauto.
  eauto.
  eauto.

  unfold size in bal.
  unfold size in gt.

  eapply IHl2.
  auto.
  eauto.

  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.

  rewrite H2 in *.
  rewrite H11 in *.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  assumption.
  assumption.

  eauto.

  (* intermediate point *)
  rewrite H2 in *.
  rewrite H11 in *.
  unfold size in bal.
  unfold size in gt.

  intro unb.
  unfold isBalanced in unb.
  unfold isBalancedSizeZ in unb.

  case (Z_le_gt_dec (deltaD * (size (join kx l2 (Bin s0 k0 r1 r2)) + 1))
          (deltaU * (size l1 + 1))).
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.

  clear unb.
  intro unb.
  rewrite H2 in unb.
  rewrite H11 in unb.

  unfold rotateL.

  case_eq (join kx l2 (Bin s0 k0 r1 r2)).
  intro jtip.
  rewrite jtip in *.
  unfold size in unb.
  fold size in unb.
  apply False_ind.
  psatzl Z.

  intros s1 k1 f f0.
  intro jlr.

  assert (Is_true (balanced (Bin s1 k1 f f0))) as jbal.
  rewrite <- jlr.
  apply IHl2.
  eauto.
  eauto.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  auto.
  auto.
  eauto.

  assert (validsize_rec (Bin s1 k1 f f0)) as vrecff0.
  rewrite <- jlr.
  eapply join_size.
  apply good5232.
  unfold p5232.
  intuition.
  eauto.
  eauto.

  unfold balanced in jbal.
  fold balanced in jbal.
  apply andb_prop_elim in jbal.
  destruct jbal as [jbal f0bal].
  apply andb_prop_elim in jbal.
  destruct jbal as [jbal fbal].
  apply andb_prop_elim in jbal.
  destruct jbal as [ff0 f0f].

  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite H2 in *.
  rewrite H11 in *.
  apply Is_true_eq_true in ff0.
  apply Is_true_eq_true in f0f.
  apply Zle_bool_imp_le in ff0.
  apply Zle_bool_imp_le in f0f.
  
  assert (s1 = size f + size f0 + 1) as s1_eq.
  assert (validsize (Bin s1 k1 f f0)).
  rewrite <- jlr.
  apply validsize_rec_self.
  eapply join_size.
  apply good5232.
  unfold p5232.
  intuition.
  eauto.
  eauto.
  unfold validsize in H10.
  unfold size in H10.
  rewrite <- H10.
  unfold realsize.
  fold realsize.
  replace (size f) with (realsize f).
  replace (size f0) with (realsize f0).
  unfold Size in *.
  psatzl Z.

  assert (validsize f0); eauto.
  assert (validsize f); eauto.

  case_eq (isSingle f f0).
  intro single.
  unfold isSingle in single.
  unfold isSingleSizeP in single.
  unfold singleL.
  unfold bin.
  unfold balanced.
  fold balanced.

  rewrite H12 in *.
  rewrite H13 in *.
  eapply Zgt_is_gt_bool in single.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold size; fold size.

  (* use join_size *)
  generalize join_size.
  intro js.
  elim js with kx l2 (Bin s0 k0 r1 r2).
  clear js.
  intro vrec.
  intro sj.
  rewrite jlr in vrec.
  rewrite jlr in sj.
  unfold size in sj.
  fold size in sj.
  rewrite jlr in unb.
  unfold size in unb.
  fold size in unb.

  unfold Size in *.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  destruct sj.
  psatzl Z.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  auto.

  apply good5232.
  unfold p5232.
  intuition.

  eauto.
  eauto.


  intro double.
  unfold isSingle in double.
  unfold isSingleSizeP in double.
  rewrite H12 in double.
  rewrite H13 in double.

  case (Z_gt_le_dec (3 * (size f0 + 1)) (2 * (size f + 1))).
  intro ggt.
  eapply Zgt_is_gt_bool in ggt.
  rewrite ggt in double.
  apply False_ind.
  clear - double.
  discriminate.

  clear double.
  intro double.

  unfold doubleL.
  destruct f.
  unfold assert_false.
  unfold size in double.
  fold size in double.
  clear fbal.
  unfold bin.
  unfold size.
  fold size.

  apply False_ind.
  generalize (size_nnegZ f0).
  intro snneg.

  assert (validsize f0).
  eauto.
  apply snneg in H10.
  clear snneg.
  psatzl Z.

  unfold size in s1_eq.
  fold size in s1_eq.

  assert (s2 = size f1 + size f2 + 1) as se_eq.
  assert (validsize (Bin s2 k2 f1 f2)).
  eauto.
  unfold validsize in H10.
  unfold size in H10.
  rewrite <- H10.
  clear H10.
  unfold realsize.
  fold realsize.
  replace (size f1) with (realsize f1).
  replace (size f2) with (realsize f2).
  unfold Size in *.
  psatzl Z.
  assert (validsize f2); eauto.
  assert (validsize f1); eauto.

  rename se_eq into s2_eq.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold size.
  fold size.

  unfold balanced in fbal.
  fold balanced in fbal.
  apply andb_prop_elim in fbal.
  destruct fbal.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  unfold isBalanced in H10.
  unfold isBalanced in H16.
  unfold isBalancedSizeZ in *.
  rewrite H2 in *.
  rewrite H11 in *.
  apply Is_true_eq_true in H10.
  apply Is_true_eq_true in H16.
  apply Zle_bool_imp_le in H10.
  apply Zle_bool_imp_le in H16.

  unfold size in double.
  fold size in double.
  unfold size in ff0.
  fold size in ff0.
  unfold size in f0f.
  fold size in f0f.

  rewrite jlr in *.
  unfold size in unb.
  fold size in unb.

  rewrite s_eq in *.
  clear s s_eq.
  rewrite s2_eq in *.
  clear s2 s2_eq.
  rewrite s1_eq in *.
  clear s1 s1_eq.
  rewrite s0_eq in *.
  clear s0 s0_eq.

  (* show iroiro >= 0 *)
  generalize (size_nnegZ f0).
  generalize (size_nnegZ f1).
  generalize (size_nnegZ f2).
  intro sf2.
  intro sf1.
  intro sf0.
  assert (validsize f0).
  eauto.
  apply sf0 in H17.
  clear sf0.
  assert (validsize f1).
  eauto.
  apply sf1 in H18.
  clear sf1.
  assert (validsize f2).
  eauto.
  apply sf2 in H19.
  clear sf2.

  (* join increases size by one at most *)
  generalize join_size.
  intro js.
  elim js with kx l2 (Bin (size r1 + size r2 + 1) k0 r1 r2).
  clear js.
  intro vrecj.
  rewrite jlr in vrecj.
  clear vrecj.
  intro sizej.
  rewrite jlr in sizej.
  unfold size in sizej.
  fold size in sizej.

  (* IHr1 and IHr2 can yield more inequalities *)

  unfold Size in *.
  

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  auto.
  auto.

  apply good5232.
  unfold p5232.
  intuition.

  eauto.
  eauto.

  (* half ended! *)
  intro unb.
  unfold isBalanced in unb.
  unfold isBalancedSizeZ in unb.
  case (Z_le_gt_dec (deltaD * (size (Bin s0 k0 r1 r2) + 1))
          (deltaU * (size (Bin s k l1 l2) + 1)) ).
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.

  clear unb.
  intro unb.
  unfold size in unb.
  fold size in unb.
  rewrite H2 in *.
  rewrite H11 in *.

  unfold join in IHr1.
  fold join in IHr1.

  generalize (join_size).
  intro js.
  elim js with kx (Bin s k l1 l2) r1.
  clear js.
  unfold join.
  fold join.

  set (inner_join :=
    ((fix join_inner (r : FSet) : FSet :=
               match r with
               | Tip => insert kx (Bin s k l1 l2)
               | Bin _ z lz rz =>
                   if isBalanced (Bin s k l1 l2) r
                   then
                    if isBalanced r (Bin s k l1 l2)
                    then bin kx (Bin s k l1 l2) r
                    else balanceL k l1 (join kx l2 r)
                   else balanceR z (join_inner lz) rz
                end) r1)) in *.

  intro vrec_ij.
  intro sij.
  unfold size in sij.
  fold size in sij.

  unfold balanceR.
  case_eq (isBalanced r2 inner_join).

  intro bbal.
  unfold isBalanced in bbal.
  unfold isBalancedSizeZ in bbal.
  apply Zle_bool_imp_le in bbal.
  rewrite H2 in *.
  rewrite H11 in *.
  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold Size in *.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  intro uunb.
  unfold isBalanced in uunb.
  unfold isBalancedSizeZ in uunb.
  rewrite H2 in *.
  rewrite H11 in *.

  case (Z_gt_le_dec (2 * (size inner_join + 1)) (5 * (size r2 + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite uunb in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear uunb.
  intro uunb.

  unfold rotateR.

  destruct inner_join.
  apply False_ind.
  clear - uunb r2nneg.
  unfold size in uunb.
  fold size in uunb.
  psatzl Z.

  assert (0 <= size inner_join1) as ij10.
  apply size_nnegZ.
  eauto.
  assert (0 <= size inner_join2) as ij20.
  apply size_nnegZ.
  eauto.

  assert (s1 = size inner_join1 + size inner_join2 + 1) as s1_eq.
  assert (validsize (Bin s1 k1 inner_join1 inner_join2)).
  eauto.
  unfold validsize in H10.
  unfold size in H10.
  rewrite <- H10.
  clear H10.
  unfold realsize.
  fold realsize.
  replace (size inner_join1) with (realsize inner_join1).
  replace (size inner_join2) with (realsize inner_join2).
  unfold Size in *.
  psatzl Z.
  assert (validsize inner_join2); eauto.
  assert (validsize inner_join1); eauto.

  unfold size in sij.
  fold size in sij.
  unfold size in uunb.
  fold size in uunb.

  unfold balanced in IHr1.
  fold balanced in IHr1.
  unfold isBalanced in IHr1.
  unfold isBalancedSizeZ in IHr1.
  rewrite H2 in *.
  rewrite H11 in *.
  apply andb_prop_elim in IHr1.
  destruct IHr1.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  apply Is_true_eq_true in H10.
  apply Is_true_eq_true in H16.
  apply Zle_bool_imp_le in H10.
  apply Zle_bool_imp_le in H16.

  case_eq (isSingle inner_join2 inner_join1).
  intro iii.
  unfold isSingle in iii.
  unfold isSingleSizeP in iii.
  rewrite H12 in iii.
  rewrite H13 in iii.
  eapply Zgt_is_gt_bool in iii.
  unfold singleR.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.
  unfold size.
  fold size.
  unfold Size in *.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  auto.
  auto.

  intro double.
  unfold isSingle in double.
  unfold isSingleSizeP in double.

  case (Z_gt_le_dec (ratioU * (size inner_join1 + 1))
             (ratioD * (size inner_join2 + 1))).
  intro gt.
  eapply Zgt_is_gt_bool in gt.
  rewrite gt in double.
  apply False_ind.
  discriminate.
  clear double.
  intro double.
  rewrite H12 in *.
  rewrite H13 in *.

  unfold doubleR.
  case_eq inner_join2.
  intro tip.
  rewrite tip in *.
  clear inner_join2 tip.
  unfold size in double.
  fold size in double.
  apply False_ind.
  psatzl Z.

  intros s2 k2 f f0.
  intro ijbin.
  assert (validsize_rec (Bin s2 k2 f f0)).
  rewrite <- ijbin.
  eauto.
  assert (s2 = size f + size f0 + 1) as s2_eq.
  assert (validsize (Bin s2 k2 f f0)).
  eauto.
  unfold validsize in H18.
  unfold realsize in H18.
  fold realsize in H18.
  unfold size in H18.
  rewrite <- H18.
  clear H18.
  replace (size f) with (realsize f).
  replace (size f0) with (realsize f0).
  unfold Size in *.
  psatzl Z.
  assert (validsize f0); eauto.
  assert (validsize f); eauto.

  rewrite ijbin in *.
  clear ijbin inner_join2.
  unfold size in ij20.

  assert (0 <= size f).
  apply size_nnegZ.
  eauto.
  assert (0 <= size f0).
  apply size_nnegZ.
  eauto.

  unfold size in H10.
  fold size in H10.

  unfold balanced in H14.
  fold balanced in H14.
  apply andb_prop_elim in H14.
  destruct H14.
  apply andb_prop_elim in H14.
  destruct H14.
  apply andb_prop_elim in H14.
  destruct H14.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite H2 in *.
  rewrite H11 in *.
  apply Is_true_eq_true in H14.
  apply Is_true_eq_true in H22.
  apply Zle_bool_imp_le in H14.
  apply Zle_bool_imp_le in H22.
  unfold size in s1_eq.
  fold size in s1_eq.
  unfold size in double.
  fold size in double.

  unfold size in H16.
  fold size in H16.

  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite H2.
  rewrite H11.

  unfold size.
  fold size.
  unfold Size in *.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  apply good5232.
  unfold p5232.
  intuition.
  eauto.
  eauto.
  Qed.

Lemma merge_size5232:
  p5232 ->
  forall (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (merge_ l r) /\
      (size (merge_ l r) = size l + size r) /\
      Is_true (balanced (merge_ l r))
    ) .
  intro gp.
  intros l r.
  generalize r.
  clear r.
  induction l.

  (* left is Tip *)
  induction r.
  intros triv triv2.
  clear triv triv2.
  intros triv triv2.
  clear triv triv2.
  split.
  compute.
  reflexivity.
  compute.
  split.
  reflexivity.
  trivial.

  (* left is Tip, right is Bin *)
  intro triv.
  intro vrec.
  intro balt.
  intro balr.
  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.
  
  destruct IHr1.
  eauto.
  eauto.
  eauto.
  eauto.

  destruct IHr2.
  eauto.
  eauto.
  eauto.
  eauto.

  unfold merge_ in *.
  split.
  eauto.
  unfold size.
  unfold Size in *.
  split.
  psatzl Z.
  unfold balanced.
  repeat (apply andb_prop_intro; split); assumption.

  (* left is Bin *)
  induction r.
  intro vrecl.
  intro triv.
  clear triv.
  intro bl.
  intro triv.
  clear triv.

  unfold merge_.
  split.
  auto.
  split.
  unfold size.
  unfold Size in *.
  psatzl Z.
  auto.

  intro vrecl.
  intro vrecr.
  intro ball.
  intro balr.
  destruct IHr1.
  auto.
  eauto.
  auto.
  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H.
  destruct H.
  auto.

  (* Both are Bin *)
  destruct IHr2.
  eauto.
  eauto.
  auto.
  unfold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H1.
  destruct H1.
  auto.
  assert (Is_true (balanced (Bin s k l1 l2))).
  auto.
  unfold balanced in H3.
  fold balanced in H3.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.

  assert (Is_true (balanced (Bin s0 k0 r1 r2))) as balr_backup.
  assumption.
  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr as [balr balr2].
  apply andb_prop_elim in balr.
  destruct balr as [balr balr1].
  apply andb_prop_elim in balr.
  destruct balr as [isbalr12 isbalr21].

  assert (s = size l1 + size l2 + 1).
  rename H3 into H33.
  assert (validsize (Bin s k l1 l2)) as H3.
  eauto.
  unfold validsize in H3.
  unfold size in H3.
  rewrite <- H3.
  clear H3.
  unfold realsize.
  fold realsize.
  replace (size l1) with (realsize l1).
  replace (size l2) with (realsize l2).
  unfold Size in *.
  psatzl Z.

  assert (validsize l2); eauto.
  assert (validsize l1); eauto.

  assert (s0 = size r1 + size r2 + 1).
  rename H4 into H44.
  assert (validsize (Bin s0 k0 r1 r2)) as H4.
  eauto.
  unfold validsize in H4.
  unfold size in H4.
  rewrite <- H4.
  unfold realsize.
  fold realsize.
  replace (size r1) with (realsize r1).
  replace (size r2) with (realsize r2).
  unfold Size in *.
  psatzl Z.
  assert (validsize r2); eauto.
  assert (validsize r1); eauto.

  unfold merge_ in *.
  fold merge_.
  fold merge_ in H1.
  fold merge_ in H2.
  fold merge_ in H0.
  fold merge_ in H.
  fold merge_ in IHl2.
  fold merge_ in IHl1.

  set (inner :=
            ((fix merge_inner (y : FSet) : FSet :=
            match y with
            | Tip => Bin s k l1 l2
            | Bin _ ky ly ry =>
                if isBalanced (Bin s k l1 l2) y
                then
                 if isBalanced y (Bin s k l1 l2)
                 then glue (Bin s k l1 l2) y
                 else balanceL ky ly (merge_ l2 y)
                else balanceR ky (merge_inner ly) ry
            end))) in *.
  unfold size in H0.
  fold size in H0.
  unfold size in H2.
  fold size in H2.

  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  unfold p5232 in gp.
  destruct gp as [gp0 gp1].
  destruct gp1 as [gp1 gp2].
  destruct gp2 as [gp2 gp3].
  rewrite gp0 in *.
  rewrite gp1 in *.

  apply Is_true_eq_true in H3.
  apply Is_true_eq_true in H6.
  apply Zle_bool_imp_le in H3.
  apply Zle_bool_imp_le in H6.
  apply Is_true_eq_true in isbalr12.
  apply Is_true_eq_true in isbalr21.
  apply Zle_bool_imp_le in isbalr12.
  apply Zle_bool_imp_le in isbalr21.

  assert (0 <= size l1) as l1nneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size l2) as l2nneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size r1) as r1nneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size r2) as r2nneg.
  apply size_nnegZ.
  eauto.

  case_eq (
    Zle_bool (2 * (size (Bin s0 k0 r1 r2) + 1))
           (5 * (size (Bin s k l1 l2) + 1))).
  intro bal.
  apply Zle_bool_imp_le in bal.
  unfold size in bal.

  case_eq (
    Zle_bool (2 * (size (Bin s k l1 l2) + 1))
           (5 * (size (Bin s0 k0 r1 r2) + 1))).
  intro bbal.
  apply Zle_bool_imp_le in bbal.
  eauto.
  unfold size in bbal.

  generalize glue_decr.
  intro gd.
  destruct gd with (Bin s k l1 l2) (Bin s0 k0 r1 r2).

  apply good5232.
  unfold p5232.
  intuition.
  eauto.
  eauto.
  eauto.
  assumption.

  apply Is_true_eq_left.
  unfold isBalanced.
  unfold size.
  unfold isBalancedSizeZ.
  apply Zle_imp_le_bool.
  rewrite gp0.
  rewrite gp1.
  assumption.

  apply Is_true_eq_left.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  unfold size.
  rewrite gp0.
  rewrite gp1.
  apply Zle_imp_le_bool.
  assumption.

  clear gd.
  intuition.

  intro ubal.
  case (Z_gt_le_dec
    (2 * (size (Bin s k l1 l2) + 1))
           (5 * (size (Bin s0 k0 r1 r2) + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite ubal in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear ubal.
  intro ubal.
  unfold size in ubal.

  split.
  eapply validsize_balanceL.
  eauto.

  eapply IHl2.
  eauto.
  eauto.
  eauto.
  eauto.

  clear inner.
  set (inner :=
                ((fix merge_inner (y : FSet) : FSet :=
                match y with
                | Tip => Bin s k l1 l2
                | Bin _ ky ly ry =>
                    if Zle_bool (2 * (size y + 1))
                         (5 * (size (Bin s k l1 l2) + 1))
                    then
                     if Zle_bool (2 * (size (Bin s k l1 l2) + 1))
                          (5 * (size y + 1))
                     then glue (Bin s k l1 l2) y
                     else balanceL ky l1 (merge_ l2 y)
                    else balanceR ky (merge_inner ly) ry
                end)))
   in *.
  
  split.
  destruct IHl2 with (Bin s0 k0 r1 r2).
  eauto.
  eauto.
  auto.
  eauto.

  rewrite size_balanceLZ.
  destruct H10.
  rewrite H10.
  unfold size.
  fold size.
  unfold Size in *.
  psatzl Z.

  eauto.
  auto.

  destruct IHl2 with (Bin s0 k0 r1 r2).
  eauto.
  eauto.
  eauto.
  eauto.
  destruct H10.

  unfold balanceL.
  case_eq (isBalanced l1 (merge_ l2 (Bin s0 k0 r1 r2))).
  intro bbal.
  unfold isBalanced in bbal.
  rewrite H10 in bbal.
  unfold size in bbal.
  fold size in bbal.
  unfold isBalancedSizeZ in bbal.
  apply Zle_bool_imp_le in bbal.
  rewrite gp0 in bbal.
  rewrite gp1 in bbal.

  unfold bin.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  rewrite H10.
  unfold size.
  fold size.
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  eauto.
  eauto.
  intro unbal.
  unfold isBalanced in unbal.
  rewrite H10 in unbal.
  unfold size in unbal.
  fold size in unbal.
  unfold isBalancedSizeZ in unbal.

  case (Z_gt_le_dec
    (deltaD * (size l2 + s0 + 1)) (deltaU * (size l1 + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unbal in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear unbal.
  rewrite gp0.
  rewrite gp1.
  intro unbal.

  unfold size in H10.
  fold size in H10.

  unfold rotateL.

  case_eq (merge_ l2 (Bin s0 k0 r1 r2)).
  intro tip.
  rewrite tip in H10.
  apply False_ind.
  unfold size in H10.
  fold size in H10.
  unfold Size in *.
  psatzl Z.

  intros s1 k1 f f0.
  intro mbin.
  rewrite mbin in *.

  assert (s1 = size f + size f0 + 1) as s1_eq.
  assert (validsize (Bin s1 k1 f f0)).
  eauto.
  unfold validsize in H12.
  unfold size in H12.
  rewrite <- H12.
  unfold realsize.
  fold realsize.
  replace (size f) with (realsize f).
  replace (size f0) with (realsize f0).
  unfold Size in *.
  psatzl Z.
  assert (validsize f0); eauto.
  assert (validsize f); eauto.

  unfold size in H10.
  fold size in H10.

  assert (0 <= size f) as fnneg.
  apply size_nnegZ.
  eauto.
  assert (0 <= size f0) as f0nneg.
  apply size_nnegZ.
  eauto.

  case_eq (isSingle f f0).
  unfold isSingle.
  unfold isSingleSizeP.
  rewrite gp2.
  rewrite gp3.
  intro single.
  eapply Zgt_is_gt_bool in single.

  unfold singleL.
  unfold bin.
  unfold size; fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  unfold size; fold size.
  unfold Size in *.

  unfold balanced in H11.
  fold balanced in H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite gp0 in *.
  rewrite gp1 in *.
  apply Is_true_eq_true in H11.
  apply Is_true_eq_true in H14.
  apply Zle_bool_imp_le in H11.
  apply Zle_bool_imp_le in H14.
  
  repeat (apply andb_prop_intro; split).

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  auto.

  intro double.
  unfold isSingle in double.
  unfold isSingleSizeP in double.
  rewrite gp2 in *.
  rewrite gp3 in *.
  case (Z_gt_le_dec (3 * (size f0 + 1)) (2 * (size f + 1))).
  intro gt.
  eapply Zgt_is_gt_bool in gt.
  rewrite double in gt.
  apply False_ind.
  discriminate.

  clear double.
  intro double.

  unfold doubleL.
  destruct f.

  unfold size in double.
  fold size in double.
  apply False_ind.
  psatzl Z.
  
  assert (s2 = size f1 + size f2 + 1) as s2_eq.
  assert (validsize (Bin s2 k2 f1 f2)).
  eauto.
  unfold validsize in H12.
  unfold size in H12.
  rewrite <- H12.
  clear H12.
  unfold realsize.
  fold realsize.
  replace (size f1) with (realsize f1).
  replace (size f2) with (realsize f2).
  unfold Size in *.
  psatzl Z.
  assert (validsize f2); eauto.
  assert (validsize f1); eauto.

  unfold size in double.
  fold size in double.
  unfold size in fnneg.
  unfold size in s1_eq.
  fold size in s1_eq.
  unfold balanced in H11.
  fold balanced in H11.
  unfold isBalanced in H11.
  unfold isBalancedSizeZ in H11.
  rewrite gp0 in *.
  rewrite gp1 in *.
  unfold size in H11.
  fold size in H11.

  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H11.
  destruct H11.
  apply andb_prop_elim in H13.
  destruct H13.
  apply andb_prop_elim in H13.
  destruct H13.
  apply andb_prop_elim in H13.
  destruct H13.

  apply Is_true_eq_true in H11.
  apply Is_true_eq_true in H14.
  apply Is_true_eq_true in H13.
  apply Is_true_eq_true in H17.
  apply Zle_bool_imp_le in H11.
  apply Zle_bool_imp_le in H13.
  apply Zle_bool_imp_le in H14.
  apply Zle_bool_imp_le in H17.

  assert (0 <= size f1).
  apply size_nnegZ.
  eauto.

  assert (0 <= size f2).
  apply size_nnegZ.
  eauto.

  unfold balanced.
  unfold bin.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  unfold size.
  fold size.
  rewrite gp0.
  rewrite gp1.
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  rewrite H7 in *.
  clear H.
  clear H0.
  clear H1 H2.
  clear inner.
  clear s H7.
  rewrite s1_eq in *.
  clear s1 s1_eq.
  clear H16 H15 H12.
  rewrite H8 in *.
  clear H8 s0.
  rewrite s2_eq in *.
  clear s2 s2_eq.
  clear H5.
  clear H4.
  clear ball.
  clear balr_backup.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  rewrite s1_eq in *.
  clear s1 s1_eq.
  rewrite s2_eq in *.
  clear s2 s2_eq.
  rewrite H7 in *.
  rewrite H8 in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.
  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.
  auto.

  intro unb.
  clear inner.
  set (inner :=
    fix merge_inner (y : FSet) : FSet :=
            match y with
            | Tip => Bin s k l1 l2
            | Bin _ ky ly ry =>
                if Zle_bool (2 * (size y + 1))
                     (5 * (size (Bin s k l1 l2) + 1))
                then
                 if Zle_bool (2 * (size (Bin s k l1 l2) + 1))
                      (5 * (size y + 1))
                 then glue (Bin s k l1 l2) y
                 else balanceL ky l1 (merge_ l2 y)
                else balanceR ky (merge_inner ly) ry
            end) in *.
  case (Z_gt_le_dec
    (2 * (size (Bin s0 k0 r1 r2) + 1))
          (5 * (size (Bin s k l1 l2) + 1))).
  Focus 2.
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unb in le.
  apply False_ind.
  discriminate.
  Unfocus.

  clear unb.
  intro unb.
  unfold size in unb.
  unfold balanceR.
  case_eq (isBalanced r2 (inner r1)).
  intro bal.
  split.
  apply validsize_rec_bin.
  auto.
  eauto.
  
  generalize bal.
  clear bal.
  unfold bin.
  unfold size.
  fold size.
  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  intro bal.
  apply Zle_bool_imp_le in bal.
  split.
  unfold Size in *.
  psatzl Z.

  unfold Size in *.
  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  intuition.
  intuition.

  intro unbal.
  split.
  apply validsize_rec_rotateR.
  auto.
  eauto.

  unfold isBalanced in unbal.
  unfold isBalancedSizeZ in unbal.

  case (Z_le_gt_dec (deltaD * (size (inner r1) + 1)) (deltaU * (size r2 + 1))).
  intro le.
  apply Zle_imp_le_bool in le.
  rewrite unbal in le.
  apply False_ind.
  discriminate.

  clear unbal.
  intro unbal.
  rewrite gp0 in *.
  rewrite gp1 in *.

  unfold rotateR.
  destruct (inner r1).
  apply False_ind.
  unfold size in unbal.
  fold size in unbal.
  psatzl Z.

  destruct H0.
  unfold size in H0.
  fold size in H0.
  move H9 at bottom.
  unfold balanced in H9.
  fold balanced in H9.
  apply andb_prop_elim in H9.
  destruct H9.
  apply andb_prop_elim in H9.
  destruct H9.
  apply andb_prop_elim in H9.
  destruct H9.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  apply Is_true_eq_true in H9.
  apply Is_true_eq_true in H12.
  apply Zle_bool_imp_le in H9.
  apply Zle_bool_imp_le in H12.

  rewrite gp0 in *.
  rewrite gp1 in *.
  
  assert (s1 = size f1 + size f2 + 1).
  assert (validsize (Bin s1 k1 f1 f2)).
  eauto.
  unfold validsize in H13.
  unfold size in H13.
  rewrite <- H13.
  unfold realsize.
  fold realsize.
  replace (size f1) with (realsize f1).
  replace (size f2) with (realsize f2).
  unfold Size in *.
  psatzl Z.

  assert (validsize f2); eauto.
  assert (validsize f1); eauto.

  unfold isSingle.
  unfold isSingleSizeP.
  rewrite gp2.
  rewrite gp3.

  assert (0<= size f1).
  apply size_nnegZ.
  eauto.

  assert (0 <= size f2).
  apply size_nnegZ.
  eauto.
  
  unfold size in unbal.
  fold size in unbal.

  case_eq (Zgt_bool (3 * (size f1 + 1)) (2 * (size f2 + 1))).
  intro single.
  eapply Zgt_is_gt_bool in single.
  unfold singleR.
  unfold bin.
  unfold size.
  fold size.


  unfold Size in *.

  split.
  psatzl Z.

  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  unfold size.
  fold size.
  rewrite gp0.
  rewrite gp1.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  unfold Size in *.
  psatzl Z.

  auto.
  auto.

  intro double.
  case (Z_gt_le_dec
    (3 * (size f1 + 1)) (2 * (size f2 + 1))).
  intro gt.
  eapply Zgt_is_gt_bool in gt.
  rewrite double in gt.
  apply False_ind.
  discriminate.
  clear double.
  intro double.

  unfold doubleR.

  destruct f2.
  apply False_ind.
  unfold size in double.
  fold size in double.
  psatzl Z.

  unfold size in double.
  fold size in double.
  unfold size in H15.
  unfold size in H13.
  fold size in H13.
  unfold size in H12.
  fold size in H12.
  unfold size in H9.
  fold size in H9.
  
  (* s2 = *)
  assert (s2 = size f2_1 + size f2_2 + 1).
  assert (validsize (Bin s2 k2 f2_1 f2_2)).
  eauto.
  unfold validsize in H16.
  unfold size in H16.
  rewrite <- H16.
  unfold realsize.
  fold realsize.
  replace (size f2_1) with (realsize f2_1).
  replace (size f2_2) with (realsize f2_2).
  unfold Size in *.
  psatzl Z.

  assert (validsize f2_2); eauto.
  assert (validsize f2_1); eauto.

  (* 0<= *)
  assert (0 <= size f2_1).
  apply size_nnegZ.
  eauto.

  assert (0 <= size f2_2).
  apply size_nnegZ.
  eauto.

  (* f2_1 f2_2 balance *)
  unfold balanced in H10.
  fold balanced in H10.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  apply andb_prop_elim in H10.
  destruct H10.
  unfold isBalanced in *.
  unfold isBalancedSizeZ in *.
  rewrite gp0 in *.
  rewrite gp1 in *.
  apply Is_true_eq_true in H10.
  apply Is_true_eq_true in H21.
  apply Zle_bool_imp_le in H10.
  apply Zle_bool_imp_le in H21.
  
  unfold bin.
  unfold size.
  fold size.
  unfold Size in *.
  split.
  psatzl Z.

  unfold balanced.
  fold balanced.
  unfold isBalanced.
  unfold isBalancedSizeZ.
  rewrite gp0.
  rewrite gp1.
  unfold size.
  fold size.

  repeat (apply andb_prop_intro; split).
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.
  
  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  apply Is_true_eq_left.
  apply Zle_imp_le_bool.
  psatzl Z.

  auto.
  auto.
  Qed.

Lemma filterGt_balanced5232:
  p5232 ->
  forall (cmplo: K->Ordering) (r1: FSet),
    validsize_rec r1 ->
    Is_true (balanced r1) ->
    Is_true (balanced (filterGt cmplo r1)).
  intro p.
  intros cmplo r.
  induction r.
  compute.
  auto.
  unfold filterGt.
  fold filterGt.
  intro vrecbin.
  intro balbin.
  unfold balanced in balbin.
  fold balanced in balbin.
  apply andb_prop_elim in balbin.
  destruct balbin.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.
  assert (Is_true (balanced (filterGt cmplo r1))).
  apply IHr1.
  eauto.
  auto.
  clear IHr1.

  assert (Is_true (balanced (filterGt cmplo r2))).
  apply IHr2.
  eauto.
  auto.
  
  case (cmplo k).
  apply join_balanced5232.
  assumption.
  auto.
  apply filterGt_vrec.
  apply good5232.
  assumption.
  eauto.
  auto.
  eauto.
  auto.
  auto.
  Qed.
  

Lemma filterLt_balanced5232:
  p5232 ->
  forall (cmplo: K->Ordering) (r1: FSet),
    validsize_rec r1 ->
    Is_true (balanced r1) ->
    Is_true (balanced (filterLt cmplo r1)).
  intro p.
  intros cmplo l.
  induction l.
  intro vall.
  intro ball.
  compute.
  trivial.

  intros vrec bal.
  unfold balanced in bal
    .
  fold balanced in bal.
  apply andb_prop_elim in bal.
  destruct bal.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.

  assert (Is_true (balanced (filterLt cmplo l1))).
  apply IHl1.
  eauto.
  eauto.
  assert (Is_true (balanced (filterLt cmplo l2))).
  apply IHl2.
  eauto.
  auto.

  unfold filterLt.
  fold filterLt.
  case (cmplo k).
  auto.
  eapply join_balanced5232.
  assumption.
  auto.
  eauto.
  auto.
  apply filterLt_vrec.
  apply good5232.
  assumption.
  eauto.
  auto.
  Qed.


Lemma hedgeunion_balance5232:
  p5232 ->
  forall (cmplo cmphi: K->Ordering) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (hedgeUnionL cmplo cmphi l r) /\
      Is_true (balanced (hedgeUnionL cmplo cmphi l r))
    ) .
  intro p.
  intros cmplo cmphi l.
  generalize cmplo cmphi.
  clear cmplo cmphi.
  induction l.
  intros cmplo cmphi.
  induction r.
  intros.
  unfold hedgeUnionL.
  intuition.

  intros.

  unfold balanced in H2.
  fold balanced in H2.
  repeat (apply andb_prop_elim in H2;   destruct H2).
  
  destruct IHr1.
  eauto.
  eauto.
  eauto.
  auto.

  destruct IHr2; eauto.

  unfold hedgeUnionL.
  split.
  eapply join_size.
  apply good5232.
  assumption.

  apply filterGt_vrec.
  apply good5232.
  assumption.
  eauto.

  apply filterLt_vrec.
  apply good5232.
  assumption.
  eauto.

  generalize join_size.
  intro js.
  destruct js with k (filterGt cmplo r1) (filterLt cmphi r2).
  apply good5232.
  assumption.

  apply filterGt_vrec.
  apply good5232; assumption.
  eauto.

  apply filterLt_vrec.
  apply good5232; assumption.
  eauto.

  clear js.

  apply join_balanced5232.
  assumption.

  apply filterGt_balanced5232.
  assumption.
  eauto.
  auto.

  apply filterGt_vrec.
  apply good5232.
  assumption.
  eauto.
  apply filterLt_balanced5232.
  assumption.
  eauto.
  auto.

  apply filterLt_vrec.
  apply good5232.
  assumption.
  eauto.

  (* left is bin *)
  intros cmplo cmphi.
  intro r.
  unfold hedgeUnionL in *.
  fold hedgeUnionL.
  fold hedgeUnionL in IHl2.
  fold hedgeUnionL in IHl1.

  intro vrecbin.
  intro vrecr.
  intro bal.
  unfold balanced in bal.
  fold balanced in bal.

  apply andb_prop_elim in bal.
  destruct bal.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.
  intro balr.
  destruct r.
  split.
  auto.
  unfold balanced.
  fold balanced.
  apply Is_true_eq_true in H.
  apply Is_true_eq_true in H2.
  apply Is_true_eq_true in H1.
  apply Is_true_eq_true in H0.
  rewrite H.
  rewrite H2.
  rewrite H1.
  rewrite H0.
  compute.
  trivial.

  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H3.
  destruct H3.
  apply andb_prop_elim in H3.
  destruct H3.

  split.
  eapply join_size.
  apply good5232.
  assumption.

  eapply IHl1.
  eauto.

  apply valsize_trim.
  eauto.
  eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro; split; auto).

  eapply IHl2; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro; split; auto).

  apply join_balanced5232; auto.
  eapply IHl1; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro ; split; auto).

  eapply IHl1; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  unfold balanced.
  repeat (apply andb_prop_intro; split; auto).

  eapply IHl2; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  repeat (apply andb_prop_intro; split; auto).

  eapply IHl2; eauto.
  apply valsize_trim; eauto.
  apply balanced_trim; eauto.
  repeat (apply andb_prop_intro; split; auto).
  Qed.


(* union operation keeps balance *)

Lemma union_balanced5232:
  p5232 ->
  forall (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (union l r) /\
      Is_true (balanced (union l r))
    ) .
  intro p.
  intros l r.
  intros.
  unfold union.

  destruct l.
  intuition.
  destruct r.
  intuition.

  eapply hedgeunion_balance5232; eauto.

  Qed.

Lemma hedgediff_balance5232:
  p5232 ->
  forall (cmplo cmphi: K->Ordering) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (hedgeDiff cmplo cmphi l r) /\
      Is_true (balanced (hedgeDiff cmplo cmphi l r))
    ) .
  intro p.
  intros cmplo cmphi l r.
  generalize l.
  clear l.
  generalize cmplo cmphi.
  clear cmplo cmphi.
  induction r.
  intros cmplo cmphi l.
  intros vrecl vrect ball balt.
  unfold hedgeDiff.
  destruct l.
  compute.
  auto.

  assert ( Is_true (balanced (Bin s k l1 l2))) as ball_bkp.
  assumption.
  unfold balanced in ball.
  fold balanced in ball.
  apply andb_prop_elim in ball.
  destruct ball.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.

  split.
  eapply join_size; eauto.
  apply good5232; auto.
  apply filterGt_vrec.
  apply good5232; auto.
  eauto.
  apply filterLt_vrec.
  apply good5232; auto.
  eauto.
  apply join_balanced5232; eauto.
  apply filterGt_balanced5232; eauto.
  apply filterGt_vrec; eauto.
  apply good5232; assumption.
  apply filterLt_balanced5232; eauto.
  apply filterLt_vrec; eauto.
  apply good5232 ;assumption.

  intros cmplo cmphi l.
  intro vrecl.
  intro vrecr.
  intro ball.
  intro balr.
  assert (Is_true (balanced (Bin s k r1 r2))) as balr_bkp.
  assumption.

  unfold balanced in balr.
  fold balanced in balr.
  apply andb_prop_elim in balr.
  destruct balr.
  apply andb_prop_elim in H.
  destruct H.
  apply andb_prop_elim in H.
  destruct H.

  unfold hedgeDiff.
  fold hedgeDiff.

  destruct l.
  intuition.

  generalize merge_size5232.
  intro ms.
  destruct ms with
            (hedgeDiff cmplo (fun k1 : X.t => COconv k k1 (X.compare k k1))
              (trim cmplo (fun k1 : X.t => COconv k k1 (X.compare k k1))
                (Bin s0 k0 l1 l2)) r1)
            (hedgeDiff (fun k1 : X.t => COconv k k1 (X.compare k k1)) cmphi
              (trim (fun k1 : X.t => COconv k k1 (X.compare k k1)) cmphi
                (Bin s0 k0 l1 l2)) r2).
  assumption.
  clear ms.
  eapply IHr1.
  apply valsize_trim; eauto.
  eauto.
  apply balanced_trim; eauto.
  eauto.

  eapply IHr2.
  apply valsize_trim; eauto.
  eauto.
  apply balanced_trim; eauto.
  eauto.

  eapply IHr1.
  apply valsize_trim.
  eauto.
  eauto.

  apply balanced_trim; eauto.
  eauto.

  eapply IHr2; eauto.
  apply valsize_trim; eauto.

  eapply balanced_trim; eauto.

  intuition.
  Qed.

(* difference operation keeps balance *)

Theorem difference_balance5232:
  p5232 ->
  forall (cmplo cmphi: K->Ordering) (l r: FSet),
    validsize_rec l ->
    validsize_rec r ->
    Is_true (balanced l) ->
    Is_true (balanced r) ->
    (validsize_rec (difference  l r) /\
      Is_true (balanced (difference l r))
    ) .
  intro p.
  intros cmplo cmphi.
  intros l r.
  intros vrecl vrecr.
  intros ball balr.
  unfold difference.
  destruct l.
  intuition.
  destruct r.
  eauto.
  apply hedgediff_balance5232; eauto.
  Qed.

Lemma splitLookupBalanced5232:
  p5232 ->
  forall (x2: K) (t1 gt_ lt_: FSet) (kx: option K),
    validsize_rec t1 ->
    Is_true (balanced t1) ->
    splitLookupWithKey x2 t1 = (lt_, kx, gt_) ->
    (validsize_rec lt_ /\
      Is_true (balanced lt_) /\
      validsize_rec gt_ /\
      Is_true (balanced gt_)).
  intro gp.
  intros x t.
  generalize x.
  clear x.
  induction t.
  unfold splitLookupWithKey.
  intros.
  simplify_eq H1.
  intros.
  rewrite <- H2.
  rewrite <- H4.
  intuition.

  unfold splitLookupWithKey.
  fold splitLookupWithKey.
  intros x r l kx.

  case (X.compare x k).
  intro lt.
  case_eq (splitLookupWithKey x t1).
  intros.
  destruct p.
  simplify_eq H2.
  clear H2.
  intros.
  rewrite H2 in *.
  clear H2 f0.
  rewrite H3 in *.
  clear o H3.
  rewrite <- H4 in *.
  clear H4 r.

  clear IHt2.
  generalize (IHt1 x f l kx).
  clear IHt1.
  intros.
  unfold balanced in H1.
  fold balanced in H1.
  apply andb_prop_elim in H1.
  destruct H1.
  apply andb_prop_elim in H1.
  destruct H1.
  
  elim H2.
  clear H2.
  intros.
  destruct H5.
  destruct H6.
  intuition.

  eapply join_size.
  apply good5232.
  assumption.
  eauto.
  eauto.
  apply join_balanced5232.
  assumption.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.

  intro xeq.
  clear xeq.
  intros.
  unfold balanced in H0.
  fold balanced in H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.

  simplify_eq H1.
  clear H1.
  intros.
  rewrite H1 in *.
  clear H1 t1.
  clear kx H5.
  rewrite H6 in *.
  clear t2 H6.
  
  intuition.

  eauto.
  eauto.

  clear IHt1.
  intro xlt.
  clear xlt.
  intros.

  unfold balanced in H0.
  fold balanced in H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.
  apply andb_prop_elim in H0.
  destruct H0.

  case_eq (splitLookupWithKey x t2).
  intros.
  rewrite H5 in H1.
  destruct p.
  simplify_eq H1.
  clear H1.
  intros.
  rewrite <- H1 in *.
  clear l H1.
  rewrite H6 in *.
  clear o H6.
  rewrite H7 in *.
  clear H7 f.

  elim IHt2 with x r f0 kx.
  clear IHt2.
  intros.
  intuition.

  eapply join_size.
  apply good5232.
  assumption.
  eauto.
  eauto.

  eapply join_balanced5232.
  assumption.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  eauto.
  assumption.
  Qed.
  
Lemma intersectionWithKey_balanced5232:
  p5232 ->
  forall (lr: FSet * FSet),
    lrbal lr (intersectionWithKey lr).
  intro p.
  apply intersectionWithKey_ind.

  (* goal 1 *)
  unfold lrbal.
  intros.
  split.
  compute.
  auto.
  compute.
  auto.

  (* goal 2 *)
  intros.
  unfold lrbal.
  intros.
  compute.
  auto.

  (* goal 3 *)
  unfold lrbal.
  intros.
  split.
  eapply join_size.
  apply good5232.
  assumption.

  eapply H.
  generalize splitLookupBalanced5232.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  auto.
  assumption.

  rewrite e0.
  assumption.
  rewrite e0.
  assumption.
  assumption.
  eauto.

  generalize splitLookupBalanced5232.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  intuition.
  assumption.

  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  reflexivity.

  eapply H0.
  eapply splitLookupBalanced5232.
  Focus 4.
  eapply e3.
  Unfocus.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  eauto.
  eapply splitLookupBalanced5232.
  Focus 4.
  apply e3.
  Unfocus.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  reflexivity.

  (* goal 4 *)
  apply join_balanced5232.
  assumption.
  eapply H.

  generalize splitLookupBalanced5232.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  auto.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  eauto.

  generalize splitLookupBalanced5232.
  intro sb.
  elim sb with x2 t1 gt_ lt_ found.
  intros.
  intuition.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  reflexivity.

  (* goal 4 *)
  eapply H.
  generalize splitLookupBalanced5232.
  intro si.
  elim si with x2 t1 gt_ lt_ found.
  intros.
  eauto.
  assumption.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.

  intros.
  eauto.
  
  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  destruct H4.
  auto.
  auto.

  eapply H0.
  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  reflexivity.

  eapply H0.
  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intros.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  auto.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  reflexivity.

  (* next goal *)
  intros.
  unfold lrbal.
  intros.
  unfold lrbal in H.
  unfold lrbal in H0.
  split.
  eapply merge_size5232.
  assumption.
  eapply H.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intro.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intro.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  apply andb_prop_elim in  H6.
  intuition.

  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply H.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  destruct H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply merge_size5232.
  assumption.

  eapply H.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  eapply H.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.
  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  reflexivity.

  eapply H0.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  eauto.

  generalize (splitLookupBalanced5232 p x2 t1 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e0.
  auto.
  rewrite e0.
  auto.
  assumption.

  unfold balanced in H4.
  apply andb_prop_elim in H4.
  intuition.

  reflexivity.

  (* next goal ... *)
  intros.
  unfold lrbal in *.
  intros.

  split.

  eapply join_size.
  apply good5232.
  assumption.

  eapply H.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eauto.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  eapply join_balanced5232.
  assumption.

  eapply H.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eauto.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  eapply H.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eauto.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  (* last goal!! *)
  intros.
  unfold lrbal in *.

  intros.

  generalize merge_size5232.
  intro ms.
  elim ms with tl tr.
  clear ms.
  intros.
  intuition.

  clear ms.
  intuition.

  eapply H.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.
  

  eapply H.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  apply andb_prop_elim in H6.
  intuition.

  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.

  eapply H0.
  eauto.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  unfold balanced in H3.
  apply andb_prop_elim in H3.
  intuition.
  
  generalize (splitLookupBalanced5232 p x1 t2 gt_ lt_ found).
  intuition.
  eapply H6.
  rewrite e1.
  auto.
  rewrite e1.
  auto.
  assumption.
  reflexivity.

  Qed.
  

(* intersection keeps balance *)
Lemma intersection_balance5232:
  p5232 ->
  forall (s1 s2 t: FSet),
      (validsize_rec s1 ->
        validsize_rec s2 ->
        Is_true (balanced s1) ->
        Is_true (balanced s2) ->
        t = intersection s1 s2 ->
        ((validsize_rec t) /\
          Is_true (balanced t))).
  unfold intersection.
  intros.
  generalize intersectionWithKey_balanced5232.
  intro iwb.
  generalize (iwb H (s1, s2)).
  intro.
  unfold lrbal in H5.
  rewrite H4.
  apply H5; eauto.
Qed.  


Extraction Language Haskell.
Recursive Extraction insert delete union difference intersection.

End FSet.

