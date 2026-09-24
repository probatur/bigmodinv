(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Completeness (bridge_complete, and bridge_complete_sharp without the redundant coprimality premise), and
   soundness and completeness as one theorem (policy_adequacy_bmi).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bmi_model_gen.
Require Import Generated.bmi_wires_gen.
Require Import Generated.bmi_scaffold_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require Import Constraints.bits_kit.
Require Import Constraints.bmi_semantic.
Require Import Constraints.bmi_soundness.
Require bmi_rule.

Lemma bitsum_ext : forall n (f g : nat -> Z),
  (forall j, (j < n)%nat -> f j = g j) -> bitsum f n = bitsum g n.
Proof.
  induction n as [|n IH]; intros f g H; [ reflexivity | ].
  cbn [bitsum]. rewrite (IH f g) by (intros j Hj; apply H; lia).
  rewrite (H n) by lia. reflexivity.
Qed.

Lemma bitsum69_bits_of : forall d, 0 <= d < 590295810358705651712 ->
  bitsum (bits_of d) 69 = d.
Proof.
  intros d [Hlo Hhi].
  rewrite (bitsum_bits_of 69 d Hlo).
  replace (wpow 69) with 590295810358705651712 by (vm_compute; reflexivity).
  apply Z.mod_small. lia.
Qed.

Lemma in_firstn_or_skipn : forall (A : Type) (n : nat) (l : list A) (x : A),
  In x l -> In x (firstn n l) \/ In x (skipn n l).
Proof.
  intros A n l x H.
  rewrite <- (firstn_skipn n l) in H.
  apply in_app_or. exact H.
Qed.

Lemma nat_split : forall k q r, (0 < k)%nat -> (r < k)%nat ->
  ((q * k + r) / k = q)%nat /\ ((q * k + r) mod k = r)%nat.
Proof.
  intros k q r Hk Hr.
  assert (Hd : ((q * k + r) / k = q)%nat).
  { rewrite Nat.div_add_l by lia. rewrite (Nat.div_small r k Hr). lia. }
  split; [ exact Hd | ].
  pose proof (Nat.div_mod_eq (q * k + r) k) as H.
  rewrite Hd in H. lia.
Qed.

Lemma list_four : forall (v : list Z), length v = 4%nat ->
  v = [nth 0 v 0; nth 1 v 0; nth 2 v 0; nth 3 v 0].
Proof.
  intros v Hl.
  destruct v as [|a [|b [|c [|d [|e v]]]]]; cbn [length] in Hl; try lia.
  reflexivity.
Qed.

Lemma VAL_four : forall v, length v = 4%nat ->
  bmi_rule.VAL v
  = nth 0 v 0
  + 18446744073709551616 * nth 1 v 0
  + 340282366920938463463374607431768211456 * nth 2 v 0
  + 6277101735386680763835789423207666416102355444464034512896 * nth 3 v 0.
Proof.
  intros v Hl.
  destruct v as [|a [|b [|c [|d [|e v]]]]]; cbn [length] in Hl; try lia.
  unfold bmi_rule.VAL. cbn [fold_right nth]. rewrite bmi_rule.B_value. ring.
Qed.

Lemma B64_le_p : 18446744073709551616 <= p.
Proof. rewrite <- wpow64_val. exact wpow64_le_p. Qed.

Section BmiWitness.

Variables inp pl out : list Z.

Definition wi0 := nth 0 inp 0.   Definition wi1 := nth 1 inp 0.
Definition wi2 := nth 2 inp 0.   Definition wi3 := nth 3 inp 0.
Definition wp0 := nth 0 pl 0.    Definition wp1 := nth 1 pl 0.
Definition wp2 := nth 2 pl 0.    Definition wp3 := nth 3 pl 0.
Definition wo0 := nth 0 out 0.   Definition wo1 := nth 1 out 0.
Definition wo2 := nth 2 out 0.   Definition wo3 := nth 3 out 0.

Definition VI := bmi_rule.VAL inp.
Definition VP := bmi_rule.VAL pl.
Definition VO := bmi_rule.VAL out.

Definition VQ := (VI * VO) / VP.

Definition Qr0 := VQ.
Definition Qr1 := Qr0 / 18446744073709551616.
Definition Qr2 := Qr1 / 18446744073709551616.
Definition Qr3 := Qr2 / 18446744073709551616.
Definition Qr4 := Qr3 / 18446744073709551616.
Definition Qr5 := Qr4 / 18446744073709551616.
Definition Qr6 := Qr5 / 18446744073709551616.
Definition Qr7 := Qr6 / 18446744073709551616.
Definition Qr8 := Qr7 / 18446744073709551616.

Definition wq0 := Qr0 - 18446744073709551616 * Qr1.
Definition wq1 := Qr1 - 18446744073709551616 * Qr2.
Definition wq2 := Qr2 - 18446744073709551616 * Qr3.
Definition wq3 := Qr3 - 18446744073709551616 * Qr4.
Definition wq4 := Qr4 - 18446744073709551616 * Qr5.
Definition wq5 := Qr5 - 18446744073709551616 * Qr6.
Definition wq6 := Qr6 - 18446744073709551616 * Qr7.
Definition wq7 := Qr7 - 18446744073709551616 * Qr8.

Definition pb0 : Z := if wp0 <? 2 then 1 else 0.
Definition wd0 : Z := wp0 - 2 + pb0 * 18446744073709551616.
Definition pb1 : Z := if wp1 <? pb0 then 1 else 0.
Definition wd1 : Z := wp1 - pb0 + pb1 * 18446744073709551616.
Definition pb2 : Z := if wp2 <? pb1 then 1 else 0.
Definition wd2 : Z := wp2 - pb1 + pb2 * 18446744073709551616.
Definition wd3 : Z := wp3 - pb2.

Definition CA0 := wi0*wo0.
Definition CA1 := wi0*wo1 + wi1*wo0.
Definition CA2 := wi0*wo2 + wi1*wo1 + wi2*wo0.
Definition CA3 := wi0*wo3 + wi1*wo2 + wi2*wo1 + wi3*wo0.
Definition CA4 := wi1*wo3 + wi2*wo2 + wi3*wo1.
Definition CA5 := wi2*wo3 + wi3*wo2.
Definition CA6 := wi3*wo3.

Definition CC0  := wq0*wp0.
Definition CC1  := wq0*wp1 + wq1*wp0.
Definition CC2  := wq0*wp2 + wq1*wp1 + wq2*wp0.
Definition CC3  := wq0*wp3 + wq1*wp2 + wq2*wp1 + wq3*wp0.
Definition CC4  := wq1*wp3 + wq2*wp2 + wq3*wp1 + wq4*wp0.
Definition CC5  := wq2*wp3 + wq3*wp2 + wq4*wp1 + wq5*wp0.
Definition CC6  := wq3*wp3 + wq4*wp2 + wq5*wp1 + wq6*wp0.
Definition CC7  := wq4*wp3 + wq5*wp2 + wq6*wp1 + wq7*wp0.
Definition CC8  := wq5*wp3 + wq6*wp2 + wq7*wp1.
Definition CC9  := wq6*wp3 + wq7*wp2.
Definition CC10 := wq7*wp3.

Definition G0  := CA0 - 1 - CC0.
Definition G1  := CA1 - CC1.
Definition G2  := CA2 - CC2.
Definition G3  := CA3 - CC3.
Definition G4  := CA4 - CC4.
Definition G5  := CA5 - CC5.
Definition G6  := CA6 - CC6.
Definition G7  := 0 - CC7.
Definition G8  := 0 - CC8.
Definition G9  := 0 - CC9.
Definition G10 := 0 - CC10.

Definition cr9  := 0 - G10.
Definition cr8  := cr9 * 18446744073709551616 - G9.
Definition cr7  := cr8 * 18446744073709551616 - G8.
Definition cr6  := cr7 * 18446744073709551616 - G7.
Definition cr5  := cr6 * 18446744073709551616 - G6.
Definition cr4  := cr5 * 18446744073709551616 - G5.
Definition cr3  := cr4 * 18446744073709551616 - G4.
Definition cr2  := cr3 * 18446744073709551616 - G3.
Definition cr1  := cr2 * 18446744073709551616 - G2.
Definition cr0  := cr1 * 18446744073709551616 - G1.

Definition crm1 := cr0 * 18446744073709551616 - G0.

Hypothesis Hpre : bmi_rule.PRE_bmi inp pl.
Hypothesis Hrel : bmi_rule.REL_bmi inp pl out.

Lemma len_inp : length inp = 4%nat.
Proof. destruct Hpre as [H _]. unfold bmi_rule.K in H. exact H. Qed.
Lemma len_pl : length pl = 4%nat.
Proof. destruct Hpre as [_ [H _]]. unfold bmi_rule.K in H. exact H. Qed.
Lemma len_out : length out = 4%nat.
Proof. destruct Hrel as [H _]. unfold bmi_rule.K in H. exact H. Qed.

Ltac limb_from H k :=
  let X := fresh in
  pose proof (H k ltac:(unfold bmi_rule.K; lia)) as X;
  rewrite bmi_rule.B_value in X.

Lemma rng_wi : 0 <= wi0 < 18446744073709551616 /\ 0 <= wi1 < 18446744073709551616
            /\ 0 <= wi2 < 18446744073709551616 /\ 0 <= wi3 < 18446744073709551616.
Proof.
  destruct Hpre as [_ [_ [H _]]].
  unfold wi0, wi1, wi2, wi3.
  limb_from H 0%nat. limb_from H 1%nat. limb_from H 2%nat. limb_from H 3%nat.
  lia.
Qed.

Lemma rng_wp : 0 <= wp0 < 18446744073709551616 /\ 0 <= wp1 < 18446744073709551616
            /\ 0 <= wp2 < 18446744073709551616 /\ 0 <= wp3 < 18446744073709551616.
Proof.
  destruct Hpre as [_ [_ [_ H]]].
  unfold wp0, wp1, wp2, wp3.
  limb_from H 0%nat. limb_from H 1%nat. limb_from H 2%nat. limb_from H 3%nat.
  lia.
Qed.

Lemma rng_wo : 0 <= wo0 < 18446744073709551616 /\ 0 <= wo1 < 18446744073709551616
            /\ 0 <= wo2 < 18446744073709551616 /\ 0 <= wo3 < 18446744073709551616.
Proof.
  destruct Hrel as [_ [H _]].
  unfold wo0, wo1, wo2, wo3.
  limb_from H 0%nat. limb_from H 1%nat. limb_from H 2%nat. limb_from H 3%nat.
  lia.
Qed.

Lemma VI_limbs : VI = wi0 + 18446744073709551616 * wi1
  + 340282366920938463463374607431768211456 * wi2
  + 6277101735386680763835789423207666416102355444464034512896 * wi3.
Proof. unfold VI, wi0, wi1, wi2, wi3. apply VAL_four, len_inp. Qed.
Lemma VP_limbs : VP = wp0 + 18446744073709551616 * wp1
  + 340282366920938463463374607431768211456 * wp2
  + 6277101735386680763835789423207666416102355444464034512896 * wp3.
Proof. unfold VP, wp0, wp1, wp2, wp3. apply VAL_four, len_pl. Qed.
Lemma VO_limbs : VO = wo0 + 18446744073709551616 * wo1
  + 340282366920938463463374607431768211456 * wo2
  + 6277101735386680763835789423207666416102355444464034512896 * wo3.
Proof. unfold VO, wo0, wo1, wo2, wo3. apply VAL_four, len_out. Qed.

Lemma VP_gt1 : 1 < VP.
Proof. destruct Hrel as [_ [_ [H _]]]. exact H. Qed.

Lemma prod_mod_is_one : (VI * VO) mod VP = 1.
Proof. destruct Hrel as [_ [_ [_ H]]]. exact H. Qed.

Lemma euclid_Z : VI * VO = VQ * VP + 1.
Proof.
  pose proof VP_gt1 as H1.
  pose proof (Z.div_mod (VI * VO) VP ltac:(lia)) as H.
  rewrite prod_mod_is_one in H. unfold VQ. lia.
Qed.

Lemma VI_nonneg : 0 <= VI.
Proof. pose proof rng_wi as R. rewrite VI_limbs. lia. Qed.
Lemma VO_nonneg : 0 <= VO.
Proof. pose proof rng_wo as R. rewrite VO_limbs. lia. Qed.

Lemma VI_lt : VI < 115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. pose proof rng_wi as R. rewrite VI_limbs. lia. Qed.
Lemma VO_lt : VO < 115792089237316195423570985008687907853269984665640564039457584007913129639936.
Proof. pose proof rng_wo as R. rewrite VO_limbs. lia. Qed.

Lemma VQ_nonneg : 0 <= VQ.
Proof.
  unfold VQ. apply Z.div_pos; [ | pose proof VP_gt1; lia ].
  pose proof VI_nonneg. pose proof VO_nonneg. nia.
Qed.

Lemma VQ_lt : VQ < 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096.
Proof.
  pose proof euclid_Z as HE. pose proof VP_gt1 as H1.
  pose proof VQ_nonneg as HQ.
  pose proof VI_nonneg. pose proof VO_nonneg.
  pose proof VI_lt. pose proof VO_lt.
  assert (HIO : VI * VO < 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096) by nia.
  nia.
Qed.

Ltac qrange_tac :=
  match goal with
  | |- 0 <= ?X - 18446744073709551616 * (?X / 18446744073709551616) < _ =>
      replace (X - 18446744073709551616 * (X / 18446744073709551616))
         with (X mod 18446744073709551616) by (rewrite Z.mod_eq by lia; ring);
      apply Z.mod_pos_bound; lia
  end.

Lemma wq0_rng : 0 <= wq0 < 18446744073709551616.
Proof. unfold wq0, Qr1, Qr0. qrange_tac. Qed.
Lemma wq1_rng : 0 <= wq1 < 18446744073709551616.
Proof. unfold wq1, Qr2. qrange_tac. Qed.
Lemma wq2_rng : 0 <= wq2 < 18446744073709551616.
Proof. unfold wq2, Qr3. qrange_tac. Qed.
Lemma wq3_rng : 0 <= wq3 < 18446744073709551616.
Proof. unfold wq3, Qr4. qrange_tac. Qed.
Lemma wq4_rng : 0 <= wq4 < 18446744073709551616.
Proof. unfold wq4, Qr5. qrange_tac. Qed.
Lemma wq5_rng : 0 <= wq5 < 18446744073709551616.
Proof. unfold wq5, Qr6. qrange_tac. Qed.
Lemma wq6_rng : 0 <= wq6 < 18446744073709551616.
Proof. unfold wq6, Qr7. qrange_tac. Qed.
Lemma wq7_rng : 0 <= wq7 < 18446744073709551616.
Proof. unfold wq7, Qr8. qrange_tac. Qed.

Lemma Qr8_zero : Qr8 = 0.
Proof.
  pose proof VQ_nonneg as H0. pose proof VQ_lt as HL.
  assert (A1 : 0 <= Qr1 < 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656).
  { unfold Qr1, Qr0. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A2 : 0 <= Qr2 < 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816).
  { unfold Qr2. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A3 : 0 <= Qr3 < 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576).
  { unfold Qr3. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A4 : 0 <= Qr4 < 115792089237316195423570985008687907853269984665640564039457584007913129639936).
  { unfold Qr4. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A5 : 0 <= Qr5 < 6277101735386680763835789423207666416102355444464034512896).
  { unfold Qr5. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A6 : 0 <= Qr6 < 340282366920938463463374607431768211456).
  { unfold Qr6. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A7 : 0 <= Qr7 < 18446744073709551616).
  { unfold Qr7. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  assert (A8 : 0 <= Qr8 < 1).
  { unfold Qr8. split; [ apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia ]. }
  lia.
Qed.

Lemma VQ_limbs : VQ = wq0 + 18446744073709551616 * wq1
  + 340282366920938463463374607431768211456 * wq2
  + 6277101735386680763835789423207666416102355444464034512896 * wq3
  + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * wq4
  + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 * wq5
  + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 * wq6
  + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656 * wq7.
Proof.
  pose proof Qr8_zero as H8.
  unfold wq0, wq1, wq2, wq3, wq4, wq5, wq6, wq7, Qr0.
  rewrite H8. ring.
Qed.

Lemma pb0_bool : pb0 = 0 \/ pb0 = 1.
Proof. unfold pb0. destruct (wp0 <? 2); auto. Qed.
Lemma pb1_bool : pb1 = 0 \/ pb1 = 1.
Proof. unfold pb1. destruct (wp1 <? pb0); auto. Qed.
Lemma pb2_bool : pb2 = 0 \/ pb2 = 1.
Proof. unfold pb2. destruct (wp2 <? pb1); auto. Qed.

Lemma pb0_cases : (pb0 = 1 /\ wp0 < 2) \/ (pb0 = 0 /\ 2 <= wp0).
Proof.
  unfold pb0. destruct (wp0 <? 2) eqn:E.
  - left. split; [ reflexivity | apply Z.ltb_lt, E ].
  - right. split; [ reflexivity | apply Z.ltb_ge, E ].
Qed.
Lemma pb1_cases : (pb1 = 1 /\ wp1 < pb0) \/ (pb1 = 0 /\ pb0 <= wp1).
Proof.
  unfold pb1. destruct (wp1 <? pb0) eqn:E.
  - left. split; [ reflexivity | apply Z.ltb_lt, E ].
  - right. split; [ reflexivity | apply Z.ltb_ge, E ].
Qed.
Lemma pb2_cases : (pb2 = 1 /\ wp2 < pb1) \/ (pb2 = 0 /\ pb1 <= wp2).
Proof.
  unfold pb2. destruct (wp2 <? pb1) eqn:E.
  - left. split; [ reflexivity | apply Z.ltb_lt, E ].
  - right. split; [ reflexivity | apply Z.ltb_ge, E ].
Qed.

Lemma wd0_rng : 0 <= wd0 < 18446744073709551616.
Proof.
  pose proof rng_wp as R. pose proof pb0_cases as C. unfold wd0. lia.
Qed.
Lemma wd1_rng : 0 <= wd1 < 18446744073709551616.
Proof.
  pose proof rng_wp as R. pose proof pb0_bool as B0. pose proof pb1_cases as C.
  unfold wd1. lia.
Qed.
Lemma wd2_rng : 0 <= wd2 < 18446744073709551616.
Proof.
  pose proof rng_wp as R. pose proof pb1_bool as B1. pose proof pb2_cases as C.
  unfold wd2. lia.
Qed.

Lemma wd3_rng : 0 <= wd3 < 18446744073709551616.
Proof.
  pose proof rng_wp as R. pose proof VP_gt1 as H1. pose proof VP_limbs as HL.
  pose proof pb2_cases as C2. pose proof pb1_cases as C1. pose proof pb0_cases as C0.
  unfold wd3. lia.
Qed.

Lemma crm1_as_residual :
  crm1 = (wq0 + 18446744073709551616 * wq1
        + 340282366920938463463374607431768211456 * wq2
        + 6277101735386680763835789423207666416102355444464034512896 * wq3
        + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * wq4
        + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 * wq5
        + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 * wq6
        + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656 * wq7)
        * (wp0 + 18446744073709551616 * wp1
        + 340282366920938463463374607431768211456 * wp2
        + 6277101735386680763835789423207666416102355444464034512896 * wp3)
        + 1
        - (wi0 + 18446744073709551616 * wi1
        + 340282366920938463463374607431768211456 * wi2
        + 6277101735386680763835789423207666416102355444464034512896 * wi3)
        * (wo0 + 18446744073709551616 * wo1
        + 340282366920938463463374607431768211456 * wo2
        + 6277101735386680763835789423207666416102355444464034512896 * wo3).
Proof.
  unfold crm1, cr0, cr1, cr2, cr3, cr4, cr5, cr6, cr7, cr8, cr9,
         G0, G1, G2, G3, G4, G5, G6, G7, G8, G9, G10,
         CA0, CA1, CA2, CA3, CA4, CA5, CA6,
         CC0, CC1, CC2, CC3, CC4, CC5, CC6, CC7, CC8, CC9, CC10.
  ring.
Qed.

Theorem the_chain_closes : crm1 = 0.
Proof.
  rewrite crm1_as_residual.
  rewrite <- VQ_limbs, <- VP_limbs, <- VI_limbs, <- VO_limbs.
  pose proof euclid_Z as H. lia.
Qed.

Definition CBND : Z := 73786976294838206472.

Lemma CBND_is_4B_plus_8 : CBND = 4 * 18446744073709551616 + 8.
Proof. unfold CBND. reflexivity. Qed.

Lemma CBND_under_2_67 : CBND < 147573952589676412928.
Proof. unfold CBND. lia. Qed.

Ltac lim := pose proof rng_wi as RI; pose proof rng_wp as RP; pose proof rng_wo as RO;
            pose proof wq0_rng; pose proof wq1_rng; pose proof wq2_rng; pose proof wq3_rng;
            pose proof wq4_rng; pose proof wq5_rng; pose proof wq6_rng; pose proof wq7_rng.

Ltac gbound :=
  lim;
  repeat match goal with
  | |- context [ ?X * ?Y ] =>
      lazymatch goal with
      | _ : 0 <= X * Y < _ |- _ => fail
      | _ => first [ pose proof (prod_bound X Y ltac:(lia) ltac:(lia)) | fail 1 ]
      end
  end;
  lia.

Lemma G0_b  : - 1361129467683753853853498429727072845824 <= G0  <= 1361129467683753853853498429727072845824.
Proof. unfold G0, CA0, CC0. gbound. Qed.
Lemma G1_b  : - 1361129467683753853853498429727072845824 <= G1  <= 1361129467683753853853498429727072845824.
Proof. unfold G1, CA1, CC1. gbound. Qed.
Lemma G2_b  : - 1361129467683753853853498429727072845824 <= G2  <= 1361129467683753853853498429727072845824.
Proof. unfold G2, CA2, CC2. gbound. Qed.
Lemma G3_b  : - 1361129467683753853853498429727072845824 <= G3  <= 1361129467683753853853498429727072845824.
Proof. unfold G3, CA3, CC3. gbound. Qed.
Lemma G4_b  : - 1361129467683753853853498429727072845824 <= G4  <= 1361129467683753853853498429727072845824.
Proof. unfold G4, CA4, CC4. gbound. Qed.
Lemma G5_b  : - 1361129467683753853853498429727072845824 <= G5  <= 1361129467683753853853498429727072845824.
Proof. unfold G5, CA5, CC5. gbound. Qed.
Lemma G6_b  : - 1361129467683753853853498429727072845824 <= G6  <= 1361129467683753853853498429727072845824.
Proof. unfold G6, CA6, CC6. gbound. Qed.
Lemma G7_b  : - 1361129467683753853853498429727072845824 <= G7  <= 1361129467683753853853498429727072845824.
Proof. unfold G7, CC7. gbound. Qed.
Lemma G8_b  : - 1361129467683753853853498429727072845824 <= G8  <= 1361129467683753853853498429727072845824.
Proof. unfold G8, CC8. gbound. Qed.
Lemma G9_b  : - 1361129467683753853853498429727072845824 <= G9  <= 1361129467683753853853498429727072845824.
Proof. unfold G9, CC9. gbound. Qed.
Lemma G10_b : - 1361129467683753853853498429727072845824 <= G10 <= 1361129467683753853853498429727072845824.
Proof. unfold G10, CC10. gbound. Qed.

Lemma rec0 : cr0 * 18446744073709551616 = crm1 + G0.
Proof. unfold crm1. ring. Qed.
Lemma rec1 : cr1 * 18446744073709551616 = cr0 + G1.
Proof. unfold cr0. ring. Qed.
Lemma rec2 : cr2 * 18446744073709551616 = cr1 + G2.
Proof. unfold cr1. ring. Qed.
Lemma rec3 : cr3 * 18446744073709551616 = cr2 + G3.
Proof. unfold cr2. ring. Qed.
Lemma rec4 : cr4 * 18446744073709551616 = cr3 + G4.
Proof. unfold cr3. ring. Qed.
Lemma rec5 : cr5 * 18446744073709551616 = cr4 + G5.
Proof. unfold cr4. ring. Qed.
Lemma rec6 : cr6 * 18446744073709551616 = cr5 + G6.
Proof. unfold cr5. ring. Qed.
Lemma rec7 : cr7 * 18446744073709551616 = cr6 + G7.
Proof. unfold cr6. ring. Qed.
Lemma rec8 : cr8 * 18446744073709551616 = cr7 + G8.
Proof. unfold cr7. ring. Qed.
Lemma rec9 : cr9 * 18446744073709551616 = cr8 + G9.
Proof. unfold cr8. ring. Qed.

Lemma cr0_b : - CBND <= cr0 <= CBND.
Proof. pose proof rec0 as R. pose proof the_chain_closes as Z0. pose proof G0_b. unfold CBND. lia. Qed.
Lemma cr1_b : - CBND <= cr1 <= CBND.
Proof. pose proof rec1 as R. pose proof cr0_b. pose proof G1_b. unfold CBND in *. lia. Qed.
Lemma cr2_b : - CBND <= cr2 <= CBND.
Proof. pose proof rec2 as R. pose proof cr1_b. pose proof G2_b. unfold CBND in *. lia. Qed.
Lemma cr3_b : - CBND <= cr3 <= CBND.
Proof. pose proof rec3 as R. pose proof cr2_b. pose proof G3_b. unfold CBND in *. lia. Qed.
Lemma cr4_b : - CBND <= cr4 <= CBND.
Proof. pose proof rec4 as R. pose proof cr3_b. pose proof G4_b. unfold CBND in *. lia. Qed.
Lemma cr5_b : - CBND <= cr5 <= CBND.
Proof. pose proof rec5 as R. pose proof cr4_b. pose proof G5_b. unfold CBND in *. lia. Qed.
Lemma cr6_b : - CBND <= cr6 <= CBND.
Proof. pose proof rec6 as R. pose proof cr5_b. pose proof G6_b. unfold CBND in *. lia. Qed.
Lemma cr7_b : - CBND <= cr7 <= CBND.
Proof. pose proof rec7 as R. pose proof cr6_b. pose proof G7_b. unfold CBND in *. lia. Qed.
Lemma cr8_b : - CBND <= cr8 <= CBND.
Proof. pose proof rec8 as R. pose proof cr7_b. pose proof G8_b. unfold CBND in *. lia. Qed.
Lemma cr9_b : - CBND <= cr9 <= CBND.
Proof. pose proof rec9 as R. pose proof cr8_b. pose proof G9_b. unfold CBND in *. lia. Qed.

Theorem every_carry_is_within_2_67 :
  - 147573952589676412928 < cr0 < 147573952589676412928 /\
  - 147573952589676412928 < cr1 < 147573952589676412928 /\
  - 147573952589676412928 < cr2 < 147573952589676412928 /\
  - 147573952589676412928 < cr3 < 147573952589676412928 /\
  - 147573952589676412928 < cr4 < 147573952589676412928 /\
  - 147573952589676412928 < cr5 < 147573952589676412928 /\
  - 147573952589676412928 < cr6 < 147573952589676412928 /\
  - 147573952589676412928 < cr7 < 147573952589676412928 /\
  - 147573952589676412928 < cr8 < 147573952589676412928 /\
  - 147573952589676412928 < cr9 < 147573952589676412928.
Proof.
  pose proof cr0_b. pose proof cr1_b. pose proof cr2_b. pose proof cr3_b.
  pose proof cr4_b. pose proof cr5_b. pose proof cr6_b. pose proof cr7_b.
  pose proof cr8_b. pose proof cr9_b. unfold CBND in *.
  repeat split; lia.
Qed.

Lemma shift_rng : forall c, - CBND <= c <= CBND ->
  0 <= c + 295147905179352825856 < 590295810358705651712.
Proof. intros c H. unfold CBND in H. lia. Qed.

Definition vc (c : nat) : Z :=
  match c with
  | 0%nat => wi0 | 1%nat => wi1 | 2%nat => wi2 | 3%nat => wi3
  | 4%nat => wp0 | 5%nat => wp1 | 6%nat => wp2 | 7%nat => wp3
  | 8%nat => wo0 | 9%nat => wo1 | 10%nat => wo2 | 11%nat => wo3
  | 12%nat => wq0 | 13%nat => wq1 | 14%nat => wq2 | 15%nat => wq3
  | 16%nat => wq4 | 17%nat => wq5 | 18%nat => wq6 | 19%nat => wq7
  | 20%nat => cr0 | 21%nat => cr1 | 22%nat => cr2 | 23%nat => cr3 | 24%nat => cr4
  | 25%nat => cr5 | 26%nat => cr6 | 27%nat => cr7 | 28%nat => cr8 | 29%nat => cr9
  | 30%nat => wd0 | 31%nat => wd1 | 32%nat => wd2 | 33%nat => wd3
  | _  => 0
  end.

Definition bitc (c : nat) : Z :=
  if (c <? 290)%nat then
    bits_of (vc (8 + (c - 34) / 64)%nat) ((c - 34) mod 64)%nat
  else if (c <? 802)%nat then
    bits_of (vc (12 + (c - 290) / 64)%nat) ((c - 290) mod 64)%nat
  else if (c <? 1492)%nat then
    bits_of (vc (20 + (c - 802) / 69)%nat + 295147905179352825856) ((c - 802) mod 69)%nat
  else if (c <? 1748)%nat then
    bits_of (vc (30 + (c - 1492) / 64)%nat) ((c - 1492) mod 64)%nat
  else if (c =? 1748)%nat then pb0
  else if (c =? 1749)%nat then pb1
  else pb2.

Lemma bitc_bool : forall c, bitc c = 0 \/ bitc c = 1.
Proof.
  intro c. unfold bitc.
  destruct (c <? 290)%nat; [ apply bits_of_bool | ].
  destruct (c <? 802)%nat; [ apply bits_of_bool | ].
  destruct (c <? 1492)%nat; [ apply bits_of_bool | ].
  destruct (c <? 1748)%nat; [ apply bits_of_bool | ].
  destruct (c =? 1748)%nat; [ apply pb0_bool | ].
  destruct (c =? 1749)%nat; [ apply pb1_bool | apply pb2_bool ].
Qed.

Definition cellv (c : nat) : Z :=
  if (c <? 34)%nat then vc c
  else if (c <? 1751)%nat then bitc c
  else 0.

Definition ASG : Assignment :=
  fun cl => if Nat.eqb (fst cl) 4000 then vc (8 + snd cl)%nat
            else if Nat.eqb (snd cl) 0 then cellv (fst cl)
            else 0.

Lemma ASG_val : forall c, (c < 34)%nat -> ASG (c, 0%nat) = vc c.
Proof.
  intros c Hc. unfold ASG. cbn [fst snd].
  rewrite (proj2 (Nat.eqb_neq c 4000) ltac:(lia)). cbn [Nat.eqb].
  unfold cellv. rewrite (proj2 (Nat.ltb_lt c 34) Hc). reflexivity.
Qed.

Lemma ASG_bit : forall c, (34 <= c < 1751)%nat -> ASG (c, 0%nat) = bitc c.
Proof.
  intros c Hc. unfold ASG. cbn [fst snd].
  rewrite (proj2 (Nat.eqb_neq c 4000) ltac:(lia)). cbn [Nat.eqb].
  unfold cellv.
  rewrite (proj2 (Nat.ltb_ge c 34) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_lt c 1751) ltac:(lia)). reflexivity.
Qed.

Lemma ASG_pub : forall j, (j < 4)%nat -> ASG (4000%nat, j) = vc (8 + j)%nat.
Proof.
  intros j Hj. unfold ASG. cbn [fst snd].
  rewrite (proj2 (Nat.eqb_eq 4000 4000) eq_refl). reflexivity.
Qed.

Lemma bat_out : forall i j, (i < 4)%nat -> (j < 64)%nat ->
  bits_at ASG (34 + 64 * i)%nat j = bits_of (vc (8 + i)%nat) j.
Proof.
  intros i j Hi Hj. unfold bits_at.
  rewrite (ASG_bit (34 + 64 * i + j)%nat ltac:(lia)).
  unfold bitc.
  rewrite (proj2 (Nat.ltb_lt (34 + 64 * i + j) 290) ltac:(lia)).
  replace (34 + 64 * i + j - 34)%nat with (i * 64 + j)%nat by lia.
  destruct (nat_split 64 i j ltac:(lia) Hj) as [Hd Hm].
  rewrite Hd, Hm. reflexivity.
Qed.

Lemma bat_q : forall i j, (i < 8)%nat -> (j < 64)%nat ->
  bits_at ASG (290 + 64 * i)%nat j = bits_of (vc (12 + i)%nat) j.
Proof.
  intros i j Hi Hj. unfold bits_at.
  rewrite (ASG_bit (290 + 64 * i + j)%nat ltac:(lia)).
  unfold bitc.
  rewrite (proj2 (Nat.ltb_ge (290 + 64 * i + j) 290) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_lt (290 + 64 * i + j) 802) ltac:(lia)).
  replace (290 + 64 * i + j - 290)%nat with (i * 64 + j)%nat by lia.
  destruct (nat_split 64 i j ltac:(lia) Hj) as [Hd Hm].
  rewrite Hd, Hm. reflexivity.
Qed.

Lemma bat_c : forall i j, (i < 10)%nat -> (j < 69)%nat ->
  bits_at ASG (802 + 69 * i)%nat j
  = bits_of (vc (20 + i)%nat + 295147905179352825856) j.
Proof.
  intros i j Hi Hj. unfold bits_at.
  rewrite (ASG_bit (802 + 69 * i + j)%nat ltac:(lia)).
  unfold bitc.
  rewrite (proj2 (Nat.ltb_ge (802 + 69 * i + j) 290) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_ge (802 + 69 * i + j) 802) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_lt (802 + 69 * i + j) 1492) ltac:(lia)).
  replace (802 + 69 * i + j - 802)%nat with (i * 69 + j)%nat by lia.
  destruct (nat_split 69 i j ltac:(lia) Hj) as [Hd Hm].
  rewrite Hd, Hm. reflexivity.
Qed.

Lemma bat_dp : forall i j, (i < 4)%nat -> (j < 64)%nat ->
  bits_at ASG (1492 + 64 * i)%nat j = bits_of (vc (30 + i)%nat) j.
Proof.
  intros i j Hi Hj. unfold bits_at.
  rewrite (ASG_bit (1492 + 64 * i + j)%nat ltac:(lia)).
  unfold bitc.
  rewrite (proj2 (Nat.ltb_ge (1492 + 64 * i + j) 290) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_ge (1492 + 64 * i + j) 802) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_ge (1492 + 64 * i + j) 1492) ltac:(lia)).
  rewrite (proj2 (Nat.ltb_lt (1492 + 64 * i + j) 1748) ltac:(lia)).
  replace (1492 + 64 * i + j - 1492)%nat with (i * 64 + j)%nat by lia.
  destruct (nat_split 64 i j ltac:(lia) Hj) as [Hd Hm].
  rewrite Hd, Hm. reflexivity.
Qed.

Ltac rec64 bat idx base cellno :=
  rewrite (bitsum_ext 64 (bits_at ASG base) (bits_of (vc cellno))
            (fun j Hj => bat idx j ltac:(lia) Hj));
  rewrite bitsum64_bits_of by (cbn [vc]; lia);
  rewrite ASG_val by lia;
  rewrite Z.sub_diag; apply Zmod_0_l.

Lemma g_rec_out : forall k, (k < 4)%nat -> gate_holds ASG (nth k tg_rec_out (EConst 0)).
Proof.
  pose proof rng_wo as RO.
  intros k Hk. unfold gate_holds.
  destruct k as [|[|[|[|k]]]]; [ | | | | lia ].
  - rewrite ev_rec_out_0. rec64 bat_out 0%nat 34%nat 8%nat.
  - rewrite ev_rec_out_1. rec64 bat_out 1%nat 98%nat 9%nat.
  - rewrite ev_rec_out_2. rec64 bat_out 2%nat 162%nat 10%nat.
  - rewrite ev_rec_out_3. rec64 bat_out 3%nat 226%nat 11%nat.
Qed.

Lemma g_rec_q : forall k, (k < 8)%nat -> gate_holds ASG (nth k tg_rec_q (EConst 0)).
Proof.
  pose proof wq0_rng. pose proof wq1_rng. pose proof wq2_rng. pose proof wq3_rng.
  pose proof wq4_rng. pose proof wq5_rng. pose proof wq6_rng. pose proof wq7_rng.
  intros k Hk. unfold gate_holds.
  destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [ | | | | | | | | lia ].
  - rewrite ev_rec_q_0. rec64 bat_q 0%nat 290%nat 12%nat.
  - rewrite ev_rec_q_1. rec64 bat_q 1%nat 354%nat 13%nat.
  - rewrite ev_rec_q_2. rec64 bat_q 2%nat 418%nat 14%nat.
  - rewrite ev_rec_q_3. rec64 bat_q 3%nat 482%nat 15%nat.
  - rewrite ev_rec_q_4. rec64 bat_q 4%nat 546%nat 16%nat.
  - rewrite ev_rec_q_5. rec64 bat_q 5%nat 610%nat 17%nat.
  - rewrite ev_rec_q_6. rec64 bat_q 6%nat 674%nat 18%nat.
  - rewrite ev_rec_q_7. rec64 bat_q 7%nat 738%nat 19%nat.
Qed.

Lemma g_rec_dp : forall k, (k < 4)%nat -> gate_holds ASG (nth k tg_rec_dp (EConst 0)).
Proof.
  pose proof wd0_rng. pose proof wd1_rng. pose proof wd2_rng. pose proof wd3_rng.
  intros k Hk. unfold gate_holds.
  destruct k as [|[|[|[|k]]]]; [ | | | | lia ].
  - rewrite ev_rec_dp_0. rec64 bat_dp 0%nat 1492%nat 30%nat.
  - rewrite ev_rec_dp_1. rec64 bat_dp 1%nat 1556%nat 31%nat.
  - rewrite ev_rec_dp_2. rec64 bat_dp 2%nat 1620%nat 32%nat.
  - rewrite ev_rec_dp_3. rec64 bat_dp 3%nat 1684%nat 33%nat.
Qed.

Ltac rec69 idx base cellno :=
  rewrite (bitsum_ext 69 (bits_at ASG base)
            (bits_of (vc cellno + 295147905179352825856))
            (fun j Hj => bat_c idx j ltac:(lia) Hj));
  rewrite bitsum69_bits_of by (cbn [vc]; lia);
  rewrite ASG_val by lia;
  rewrite Z.sub_diag; apply Zmod_0_l.

Lemma g_rec_c : forall k, (k < 10)%nat -> gate_holds ASG (nth k tg_rec_c (EConst 0)).
Proof.
  pose proof cr0_b. pose proof cr1_b. pose proof cr2_b. pose proof cr3_b.
  pose proof cr4_b. pose proof cr5_b. pose proof cr6_b. pose proof cr7_b.
  pose proof cr8_b. pose proof cr9_b. unfold CBND in *.
  intros k Hk. unfold gate_holds.
  destruct k as [|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]; [ | | | | | | | | | | lia ].
  - rewrite ev_rec_c_0. rec69 0%nat 802%nat 20%nat.
  - rewrite ev_rec_c_1. rec69 1%nat 871%nat 21%nat.
  - rewrite ev_rec_c_2. rec69 2%nat 940%nat 22%nat.
  - rewrite ev_rec_c_3. rec69 3%nat 1009%nat 23%nat.
  - rewrite ev_rec_c_4. rec69 4%nat 1078%nat 24%nat.
  - rewrite ev_rec_c_5. rec69 5%nat 1147%nat 25%nat.
  - rewrite ev_rec_c_6. rec69 6%nat 1216%nat 26%nat.
  - rewrite ev_rec_c_7. rec69 7%nat 1285%nat 27%nat.
  - rewrite ev_rec_c_8. rec69 8%nat 1354%nat 28%nat.
  - rewrite ev_rec_c_9. rec69 9%nat 1423%nat 29%nat.
Qed.

Ltac cellsub := repeat (rewrite ASG_val by lia); cbn [vc].

Lemma g_chain : forall k, (k < 11)%nat -> gate_holds ASG (nth k tg_chain (EConst 0)).
Proof.
  intros k Hk. unfold gate_holds.
  destruct k as [|[|[|[|[|[|[|[|[|[|[|k]]]]]]]]]]]; [ | | | | | | | | | | | lia ].
  - rewrite ev_chain_0. unfold R0. cellsub.
    replace (wi0 * wo0 - wq0 * wp0 - 1 - cr0 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ].
    pose proof the_chain_closes as H. unfold crm1, G0, CA0, CC0 in H. lia.
  - rewrite ev_chain_1. unfold R1. cellsub.
    replace (wi0 * wo1 + wi1 * wo0 - (wq0 * wp1 + wq1 * wp0) + cr0 - cr1 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr0, G1, CA1, CC1. ring.
  - rewrite ev_chain_2. unfold R2. cellsub.
    replace (wi0 * wo2 + wi1 * wo1 + wi2 * wo0 - (wq0 * wp2 + wq1 * wp1 + wq2 * wp0) + cr1 - cr2 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr1, G2, CA2, CC2. ring.
  - rewrite ev_chain_3. unfold R3. cellsub.
    replace (wi0 * wo3 + wi1 * wo2 + wi2 * wo1 + wi3 * wo0 - (wq0 * wp3 + wq1 * wp2 + wq2 * wp1 + wq3 * wp0) + cr2 - cr3 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr2, G3, CA3, CC3. ring.
  - rewrite ev_chain_4. unfold R4. cellsub.
    replace (wi1 * wo3 + wi2 * wo2 + wi3 * wo1 - (wq1 * wp3 + wq2 * wp2 + wq3 * wp1 + wq4 * wp0) + cr3 - cr4 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr3, G4, CA4, CC4. ring.
  - rewrite ev_chain_5. unfold R5. cellsub.
    replace (wi2 * wo3 + wi3 * wo2 - (wq2 * wp3 + wq3 * wp2 + wq4 * wp1 + wq5 * wp0) + cr4 - cr5 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr4, G5, CA5, CC5. ring.
  - rewrite ev_chain_6. unfold R6. cellsub.
    replace (wi3 * wo3 - (wq3 * wp3 + wq4 * wp2 + wq5 * wp1 + wq6 * wp0) + cr5 - cr6 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr5, G6, CA6, CC6. ring.
  - rewrite ev_chain_7. unfold R7. cellsub.
    replace (0 - (wq4 * wp3 + wq5 * wp2 + wq6 * wp1 + wq7 * wp0) + cr6 - cr7 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr6, G7, CC7. ring.
  - rewrite ev_chain_8. unfold R8. cellsub.
    replace (0 - (wq5 * wp3 + wq6 * wp2 + wq7 * wp1) + cr7 - cr8 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr7, G8, CC8. ring.
  - rewrite ev_chain_9. unfold R9. cellsub.
    replace (0 - (wq6 * wp3 + wq7 * wp2) + cr8 - cr9 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold cr8, G9, CC9. ring.
  - rewrite ev_chain_10. unfold R10. cellsub.
    replace (0 - wq7 * wp3 + cr9) with 0;
      [ apply Zmod_0_l | ]. unfold cr9, G10, CC10. ring.
Qed.

Lemma g_pchain : forall k, (k < 4)%nat -> gate_holds ASG (nth k tg_pchain (EConst 0)).
Proof.
  intros k Hk. unfold gate_holds.
  destruct k as [|[|[|[|k]]]]; [ | | | | lia ].
  - rewrite ev_pchain_0. unfold PR0.
    rewrite (ASG_val 30%nat ltac:(lia)), (ASG_val 4%nat ltac:(lia)),
            (ASG_bit 1748%nat ltac:(lia)). cbn [vc].
    replace (bitc 1748) with pb0 by (unfold bitc; reflexivity).
    replace (wd0 - wp0 + 2 - pb0 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold wd0. ring.
  - rewrite ev_pchain_1. unfold PR1.
    rewrite (ASG_val 31%nat ltac:(lia)), (ASG_val 5%nat ltac:(lia)),
            (ASG_bit 1748%nat ltac:(lia)), (ASG_bit 1749%nat ltac:(lia)). cbn [vc].
    replace (bitc 1748) with pb0 by (unfold bitc; reflexivity).
    replace (bitc 1749) with pb1 by (unfold bitc; reflexivity).
    replace (wd1 - wp1 + pb0 - pb1 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold wd1. ring.
  - rewrite ev_pchain_2. unfold PR2.
    rewrite (ASG_val 32%nat ltac:(lia)), (ASG_val 6%nat ltac:(lia)),
            (ASG_bit 1749%nat ltac:(lia)), (ASG_bit 1750%nat ltac:(lia)). cbn [vc].
    replace (bitc 1749) with pb1 by (unfold bitc; reflexivity).
    replace (bitc 1750) with pb2 by (unfold bitc; reflexivity).
    replace (wd2 - wp2 + pb1 - pb2 * 18446744073709551616) with 0;
      [ apply Zmod_0_l | ]. unfold wd2. ring.
  - rewrite ev_pchain_3. unfold PR3.
    rewrite (ASG_val 33%nat ltac:(lia)), (ASG_val 7%nat ltac:(lia)),
            (ASG_bit 1750%nat ltac:(lia)). cbn [vc].
    replace (bitc 1750) with pb2 by (unfold bitc; reflexivity).
    replace (wd3 - wp3 + pb2) with 0;
      [ apply Zmod_0_l | ]. unfold wd3. ring.
Qed.

Lemma g_bool : forall j, (j < 1717)%nat -> gate_holds ASG (bool_gate (34 + j)%nat).
Proof.
  intros j Hj. unfold gate_holds, bool_gate. cbn [eval].
  rewrite (ASG_bit (34 + j)%nat ltac:(lia)).
  destruct (bitc_bool (34 + j)%nat) as [E|E]; rewrite E;
    [ replace (0 * (0 - 1)) with 0 by ring | replace (1 * (1 - 1)) with 0 by ring ];
    apply Zmod_0_l.
Qed.

Theorem all_gates_hold : gates_hold ASG deployed_gates.
Proof.
  intros g Hin.
  destruct (in_firstn_or_skipn _ 1717 deployed_gates g Hin) as [Hh|Ht].
  - rewrite head_is_the_booleanity_bank in Hh.
    apply in_map_iff in Hh. destruct Hh as [j [Hj Hseq]].
    apply in_seq in Hseq. subst g. apply g_bool. lia.
  - change (skipn 1717 deployed_gates) with tail_gates in Ht.
    rewrite <- tail_split_is_a_partition in Ht.
    repeat (apply in_app_or in Ht; destruct Ht as [Ht|Ht]).
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_out_len in Hk. subst g. apply g_rec_out; exact Hk.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_q_len in Hk. subst g. apply g_rec_q; exact Hk.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_c_len in Hk. subst g. apply g_rec_c; exact Hk.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_rec_dp_len in Hk. subst g. apply g_rec_dp; exact Hk.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_chain_len in Hk. subst g. apply g_chain; exact Hk.
    + apply (In_nth _ _ (EConst 0)) in Ht. destruct Ht as [k [Hk Hg]].
      rewrite tg_pchain_len in Hk. subst g. apply g_pchain; exact Hk.
Qed.

Theorem all_copies_hold : copy_holds ASG deployed_copy.
Proof.
  intros e Hin. cbn [deployed_copy In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
  - rewrite (ASG_val 8%nat ltac:(lia)), (ASG_pub 0%nat ltac:(lia)). reflexivity.
  - rewrite (ASG_val 9%nat ltac:(lia)), (ASG_pub 1%nat ltac:(lia)). reflexivity.
  - rewrite (ASG_val 10%nat ltac:(lia)), (ASG_pub 2%nat ltac:(lia)). reflexivity.
  - rewrite (ASG_val 11%nat ltac:(lia)), (ASG_pub 3%nat ltac:(lia)). reflexivity.
Qed.

Theorem ASG_sat : sat deployed_model ASG.
Proof. split; [ exact all_gates_hold | exact all_copies_hold ]. Qed.

Lemma dc_val : forall c, (c < 34)%nat -> 0 <= vc c < 18446744073709551616 ->
  dc ASG c = vc c.
Proof.
  intros c Hc Hr. unfold dc. rewrite (ASG_val c Hc).
  apply Z.mod_small. pose proof B64_le_p. lia.
Qed.

Lemma decode_inp : inp_l ASG = inp.
Proof.
  pose proof rng_wi as R.
  unfold inp_l.
  rewrite (dc_val 0%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 1%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 2%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 3%nat ltac:(lia) ltac:(cbn [vc]; lia)).
  cbn [vc]. unfold wi0, wi1, wi2, wi3.
  symmetry. apply list_four, len_inp.
Qed.

Lemma decode_pl : p_l ASG = pl.
Proof.
  pose proof rng_wp as R.
  unfold p_l.
  rewrite (dc_val 4%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 5%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 6%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 7%nat ltac:(lia) ltac:(cbn [vc]; lia)).
  cbn [vc]. unfold wp0, wp1, wp2, wp3.
  symmetry. apply list_four, len_pl.
Qed.

Lemma decode_out : out_l ASG = out.
Proof.
  pose proof rng_wo as R.
  unfold out_l.
  rewrite (dc_val 8%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 9%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 10%nat ltac:(lia) ltac:(cbn [vc]; lia)),
          (dc_val 11%nat ltac:(lia) ltac:(cbn [vc]; lia)).
  cbn [vc]. unfold wo0, wo1, wo2, wo3.
  symmetry. apply list_four, len_out.
Qed.

Theorem witness_exists :
  sat deployed_model ASG
  /\ CANON_bmi ASG
  /\ bmi_rule.PRE_bmi (inp_l ASG) (p_l ASG)
  /\ inp_l ASG = inp /\ p_l ASG = pl /\ out_l ASG = out.
Proof.
  split; [ exact ASG_sat | ].
  split; [ apply CANON_is_free | ].
  split; [ rewrite decode_inp, decode_pl; exact Hpre | ].
  split; [ exact decode_inp | ].
  split; [ exact decode_pl | exact decode_out ].
Qed.

End BmiWitness.

Theorem the_gcd_premise_is_a_THEOREM : forall inp pl out,
  bmi_rule.PRE_bmi inp pl ->
  bmi_rule.REL_bmi inp pl out ->
  Z.gcd (bmi_rule.VAL inp) (bmi_rule.VAL pl) = 1.
Proof.
  intros inp pl out Hpre Hrel.
  exact (bmi_rule.accepted_rows_are_coprime inp pl out Hrel).
Qed.

(* Completeness in the shape of the statement: for every triple that satisfies the input assumption
   and that the rule accepts, a filling the circuit accepts that reads back as exactly that triple,
   the given output included. *)
Theorem bridge_complete : forall inp pl out,
  bmi_rule.PRE_bmi inp pl ->
  bmi_rule.R_bmi inp pl out ->
  Z.gcd (bmi_rule.VAL inp) (bmi_rule.VAL pl) = 1 ->
  exists al,
    sat deployed_model al
    /\ CANON_bmi al
    /\ bmi_rule.PRE_bmi (inp_l al) (p_l al)
    /\ inp_l al = inp /\ p_l al = pl /\ out_l al = out.
Proof.
  intros inp pl out Hpre HR _.
  exists (ASG inp pl out).
  exact (witness_exists inp pl out Hpre (HR Hpre)).
Qed.

(* The same without the coprimality premise, which is redundant (the_gcd_premise_is_a_THEOREM).
   This is the form to quote. *)
Theorem bridge_complete_sharp : forall inp pl out,
  bmi_rule.PRE_bmi inp pl ->
  bmi_rule.R_bmi inp pl out ->
  exists al,
    sat deployed_model al
    /\ CANON_bmi al
    /\ bmi_rule.PRE_bmi (inp_l al) (p_l al)
    /\ inp_l al = inp /\ p_l al = pl /\ out_l al = out.
Proof.
  intros inp pl out Hpre HR.
  exists (ASG inp pl out).
  exact (witness_exists inp pl out Hpre (HR Hpre)).
Qed.

(* Soundness and completeness as one theorem. The left conjunct alone would hold of a circuit that
   accepts nothing, the right alone of one that accepts everything; only the pair pins the accepted
   set to the rule's. *)
Theorem policy_adequacy_bmi :

  (forall a,
     sat deployed_model a ->
     CANON_bmi a ->
     bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
     bmi_rule.REL_bmi (inp_l a) (p_l a) (out_l a))
  /\

  (forall inp pl out,
     bmi_rule.PRE_bmi inp pl ->
     bmi_rule.R_bmi inp pl out ->
     Z.gcd (bmi_rule.VAL inp) (bmi_rule.VAL pl) = 1 ->
     exists al,
       sat deployed_model al
       /\ CANON_bmi al
       /\ bmi_rule.PRE_bmi (inp_l al) (p_l al)
       /\ inp_l al = inp /\ p_l al = pl /\ out_l al = out).
Proof.
  split; [ exact bridge_sound | exact bridge_complete ].
Qed.

Theorem completeness_hypothesis_is_INHABITED :
  bmi_rule.PRE_bmi bmi_rule.INP_ANCHOR bmi_rule.P_ANCHOR
  /\ bmi_rule.R_bmi bmi_rule.INP_ANCHOR bmi_rule.P_ANCHOR bmi_rule.OUT_ANCHOR.
Proof.
  split; [ exact bmi_rule.anchor_pre | ].
  intros _. exact bmi_rule.R_bmi_real_inverse_accepted.
Qed.

(* An instance shown, not the evidence: the construction at a second accepted output for the same
   inputs. Completeness itself is universal. *)
Theorem completeness_admits_the_SECOND_representative :
  exists al,
    sat deployed_model al
    /\ out_l al = bmi_rule.OUT2_ANCHOR
    /\ inp_l al = bmi_rule.INP_ANCHOR
    /\ p_l al = bmi_rule.P_ANCHOR.
Proof.
  destruct (bridge_complete_sharp bmi_rule.INP_ANCHOR bmi_rule.P_ANCHOR
              bmi_rule.OUT2_ANCHOR bmi_rule.anchor_pre
              (fun _ => bmi_rule.R_bmi_second_representative_ALSO_accepted))
    as [al [Hs [_ [_ [Hi [Hp Ho]]]]]].
  exists al. split; [ exact Hs | ]. split; [ exact Ho | ].
  split; [ exact Hi | exact Hp ].
Qed.

Print Assumptions bridge_complete.
Print Assumptions bridge_complete_sharp.
Print Assumptions policy_adequacy_bmi.
Print Assumptions the_gcd_premise_is_a_THEOREM.
Print Assumptions completeness_hypothesis_is_INHABITED.
Print Assumptions completeness_admits_the_SECOND_representative.
