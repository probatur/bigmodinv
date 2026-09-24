(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Soundness: every accepted filling whose operands satisfy the input assumption yields a triple the rule
   accepts (bridge_sound). It includes the comparator argument: for an accepted filling whose operands
   satisfy the input assumption, the value of p is 2 more than the value of four in-range limbs
   (comparator_forces_the_modulus), so it exceeds 1 (modulus_exceeds_one).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bmi_model_gen.
Require Import Generated.bmi_wires_gen.
Require Import Generated.bmi_scaffold_gen.
Require Import Generated.bmi_necessity_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require Import Constraints.bmi_semantic.
Require bmi_rule.

Definition bits_at (a : Assignment) (b : nat) : nat -> Z :=
  fun j => a ((b + j)%nat, 0%nat).

Definition cc (a : Assignment) (m : nat) : Z :=
  ((a ((20 + m)%nat, 0%nat) + 295147905179352825856) mod p) - 295147905179352825856.

Lemma cong_cc : forall a m, (cc a m) mod p = (a ((20 + m)%nat, 0%nat)) mod p.
Proof.
  intros a m. unfold cc.
  rewrite Zminus_mod_idemp_l.
  f_equal. ring.
Qed.

Lemma bank_bits_boolean : forall a,
  sat deployed_model a ->
  forall b n, (34 <= b)%nat -> (b + n <= 1751)%nat ->
  forall j, (j < n)%nat ->
    (bits_at a b j) mod p = 0 \/ (bits_at a b j) mod p = 1.
Proof.
  intros a Hs b n Hb Hbn j Hj. unfold bits_at.
  replace (b + j)%nat with (34 + (b - 34 + j))%nat by lia.
  apply (every_bit_cell_is_boolean a Hs). lia.
Qed.

Lemma wpow64_le_p : wpow 64 <= p.
Proof. rewrite p_eq_pasta. exact wpow64_le_pasta. Qed.
Lemma wpow69_le_p : wpow 69 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.
Lemma wpow64_val : wpow 64 = 18446744073709551616.
Proof. vm_compute. reflexivity. Qed.
Lemma wpow69_val : wpow 69 = 590295810358705651712.
Proof. vm_compute. reflexivity. Qed.

Lemma range_from_gate : forall a b n v,
  sat deployed_model a ->
  (34 <= b)%nat -> (b + n <= 1751)%nat ->
  wpow n <= p ->
  (bitsum (bits_at a b) n - v) mod p = 0 ->
  0 <= v mod p < wpow n.
Proof.
  intros a b n v Hs Hb Hbn Hw Hres.
  destruct (order_lift p p_ge2 (bits_at a b) n v Hw
              (bank_bits_boolean a Hs b n Hb Hbn) Hres) as [_ Hr].
  exact Hr.
Qed.

Lemma cong_add : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x + y) mod p = (x' + y') mod p.
Proof. intros. rewrite Zplus_mod, H, H0, <- Zplus_mod. reflexivity. Qed.
Lemma cong_sub : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x - y) mod p = (x' - y') mod p.
Proof. intros. rewrite Zminus_mod, H, H0, <- Zminus_mod. reflexivity. Qed.
Lemma cong_mul : forall x y x' y', x mod p = x' mod p -> y mod p = y' mod p ->
  (x * y) mod p = (x' * y') mod p.
Proof. intros. rewrite Zmult_mod, H, H0, <- Zmult_mod. reflexivity. Qed.
Lemma cong_opp : forall x x', x mod p = x' mod p -> (- x) mod p = (- x') mod p.
Proof.
  intros x x' H.
  replace (- x) with (0 - x) by ring. replace (- x') with (0 - x') by ring.
  rewrite Zminus_mod, H, <- Zminus_mod. reflexivity.
Qed.
Lemma cong_dc : forall a c, (dc a c) mod p = (a (c, 0%nat)) mod p.
Proof. intros. unfold dc. apply Zmod_mod. Qed.

Ltac cong := repeat first
  [ apply cong_dc | apply cong_cc | apply cong_opp
  | apply cong_mul | apply cong_sub | apply cong_add | reflexivity ].

Lemma ev_rec_out_0 : forall a, eval a (nth 0 tg_rec_out (EConst 0))
  = bitsum (bits_at a 34) 64 - a (8%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_1 : forall a, eval a (nth 1 tg_rec_out (EConst 0))
  = bitsum (bits_at a 98) 64 - a (9%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_2 : forall a, eval a (nth 2 tg_rec_out (EConst 0))
  = bitsum (bits_at a 162) 64 - a (10%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_out_3 : forall a, eval a (nth 3 tg_rec_out (EConst 0))
  = bitsum (bits_at a 226) 64 - a (11%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_out eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_0 : forall a, eval a (nth 0 tg_rec_q (EConst 0))
  = bitsum (bits_at a 290) 64 - a (12%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_1 : forall a, eval a (nth 1 tg_rec_q (EConst 0))
  = bitsum (bits_at a 354) 64 - a (13%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_2 : forall a, eval a (nth 2 tg_rec_q (EConst 0))
  = bitsum (bits_at a 418) 64 - a (14%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_3 : forall a, eval a (nth 3 tg_rec_q (EConst 0))
  = bitsum (bits_at a 482) 64 - a (15%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_4 : forall a, eval a (nth 4 tg_rec_q (EConst 0))
  = bitsum (bits_at a 546) 64 - a (16%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_5 : forall a, eval a (nth 5 tg_rec_q (EConst 0))
  = bitsum (bits_at a 610) 64 - a (17%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_6 : forall a, eval a (nth 6 tg_rec_q (EConst 0))
  = bitsum (bits_at a 674) 64 - a (18%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_q_7 : forall a, eval a (nth 7 tg_rec_q (EConst 0))
  = bitsum (bits_at a 738) 64 - a (19%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_q eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_0 : forall a, eval a (nth 0 tg_rec_c (EConst 0))
  = bitsum (bits_at a 802) 69 - (a (20%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_1 : forall a, eval a (nth 1 tg_rec_c (EConst 0))
  = bitsum (bits_at a 871) 69 - (a (21%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_2 : forall a, eval a (nth 2 tg_rec_c (EConst 0))
  = bitsum (bits_at a 940) 69 - (a (22%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_3 : forall a, eval a (nth 3 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1009) 69 - (a (23%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_4 : forall a, eval a (nth 4 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1078) 69 - (a (24%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_5 : forall a, eval a (nth 5 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1147) 69 - (a (25%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_6 : forall a, eval a (nth 6 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1216) 69 - (a (26%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_7 : forall a, eval a (nth 7 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1285) 69 - (a (27%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_8 : forall a, eval a (nth 8 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1354) 69 - (a (28%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_c_9 : forall a, eval a (nth 9 tg_rec_c (EConst 0))
  = bitsum (bits_at a 1423) 69 - (a (29%nat, 0%nat) + 295147905179352825856).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_c eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_dp_0 : forall a, eval a (nth 0 tg_rec_dp (EConst 0))
  = bitsum (bits_at a 1492) 64 - a (30%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_dp eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_dp_1 : forall a, eval a (nth 1 tg_rec_dp (EConst 0))
  = bitsum (bits_at a 1556) 64 - a (31%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_dp eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_dp_2 : forall a, eval a (nth 2 tg_rec_dp (EConst 0))
  = bitsum (bits_at a 1620) 64 - a (32%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_dp eval bitsum wpow Nat.add]. ring. Qed.
Lemma ev_rec_dp_3 : forall a, eval a (nth 3 tg_rec_dp (EConst 0))
  = bitsum (bits_at a 1684) 64 - a (33%nat, 0%nat).
Proof. intro a. unfold bits_at. cbn [nth tg_rec_dp eval bitsum wpow Nat.add]. ring. Qed.

Lemma rng_out_0 : forall a, sat deployed_model a ->
  0 <= (a (8%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 34 64 (a (8%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_out_0.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_out_in 0 ltac:(lia))).
Qed.
Lemma rng_out_1 : forall a, sat deployed_model a ->
  0 <= (a (9%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 98 64 (a (9%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_out_1.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_out_in 1 ltac:(lia))).
Qed.
Lemma rng_out_2 : forall a, sat deployed_model a ->
  0 <= (a (10%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 162 64 (a (10%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_out_2.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_out_in 2 ltac:(lia))).
Qed.
Lemma rng_out_3 : forall a, sat deployed_model a ->
  0 <= (a (11%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 226 64 (a (11%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_out_3.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_out_in 3 ltac:(lia))).
Qed.
Lemma rng_q_0 : forall a, sat deployed_model a ->
  0 <= (a (12%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 290 64 (a (12%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_0.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 0 ltac:(lia))).
Qed.
Lemma rng_q_1 : forall a, sat deployed_model a ->
  0 <= (a (13%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 354 64 (a (13%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_1.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 1 ltac:(lia))).
Qed.
Lemma rng_q_2 : forall a, sat deployed_model a ->
  0 <= (a (14%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 418 64 (a (14%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_2.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 2 ltac:(lia))).
Qed.
Lemma rng_q_3 : forall a, sat deployed_model a ->
  0 <= (a (15%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 482 64 (a (15%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_3.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 3 ltac:(lia))).
Qed.
Lemma rng_q_4 : forall a, sat deployed_model a ->
  0 <= (a (16%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 546 64 (a (16%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_4.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 4 ltac:(lia))).
Qed.
Lemma rng_q_5 : forall a, sat deployed_model a ->
  0 <= (a (17%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 610 64 (a (17%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_5.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 5 ltac:(lia))).
Qed.
Lemma rng_q_6 : forall a, sat deployed_model a ->
  0 <= (a (18%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 674 64 (a (18%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_6.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 6 ltac:(lia))).
Qed.
Lemma rng_q_7 : forall a, sat deployed_model a ->
  0 <= (a (19%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 738 64 (a (19%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_q_7.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_q_in 7 ltac:(lia))).
Qed.
Lemma rng_c_0 : forall a, sat deployed_model a ->
  0 <= ((a (20%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 802 69 ((a (20%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_0.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 0 ltac:(lia))).
Qed.
Lemma rng_c_1 : forall a, sat deployed_model a ->
  0 <= ((a (21%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 871 69 ((a (21%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_1.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 1 ltac:(lia))).
Qed.
Lemma rng_c_2 : forall a, sat deployed_model a ->
  0 <= ((a (22%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 940 69 ((a (22%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_2.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 2 ltac:(lia))).
Qed.
Lemma rng_c_3 : forall a, sat deployed_model a ->
  0 <= ((a (23%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1009 69 ((a (23%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_3.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 3 ltac:(lia))).
Qed.
Lemma rng_c_4 : forall a, sat deployed_model a ->
  0 <= ((a (24%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1078 69 ((a (24%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_4.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 4 ltac:(lia))).
Qed.
Lemma rng_c_5 : forall a, sat deployed_model a ->
  0 <= ((a (25%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1147 69 ((a (25%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_5.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 5 ltac:(lia))).
Qed.
Lemma rng_c_6 : forall a, sat deployed_model a ->
  0 <= ((a (26%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1216 69 ((a (26%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_6.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 6 ltac:(lia))).
Qed.
Lemma rng_c_7 : forall a, sat deployed_model a ->
  0 <= ((a (27%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1285 69 ((a (27%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_7.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 7 ltac:(lia))).
Qed.
Lemma rng_c_8 : forall a, sat deployed_model a ->
  0 <= ((a (28%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1354 69 ((a (28%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_8.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 8 ltac:(lia))).
Qed.
Lemma rng_c_9 : forall a, sat deployed_model a ->
  0 <= ((a (29%nat, 0%nat) + 295147905179352825856)) mod p < 590295810358705651712.
Proof.
  intros a Hs. rewrite <- wpow69_val.
  apply (range_from_gate a 1423 69 ((a (29%nat, 0%nat) + 295147905179352825856)) Hs); [ lia | lia | exact wpow69_le_p | ].
  rewrite <- ev_rec_c_9.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_c_in 9 ltac:(lia))).
Qed.
Lemma rng_dp_0 : forall a, sat deployed_model a ->
  0 <= (a (30%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 1492 64 (a (30%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_dp_0.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_dp_in 0 ltac:(lia))).
Qed.
Lemma rng_dp_1 : forall a, sat deployed_model a ->
  0 <= (a (31%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 1556 64 (a (31%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_dp_1.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_dp_in 1 ltac:(lia))).
Qed.
Lemma rng_dp_2 : forall a, sat deployed_model a ->
  0 <= (a (32%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 1620 64 (a (32%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_dp_2.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_dp_in 2 ltac:(lia))).
Qed.
Lemma rng_dp_3 : forall a, sat deployed_model a ->
  0 <= (a (33%nat, 0%nat)) mod p < 18446744073709551616.
Proof.
  intros a Hs. rewrite <- wpow64_val.
  apply (range_from_gate a 1684 64 (a (33%nat, 0%nat)) Hs); [ lia | lia | exact wpow64_le_p | ].
  rewrite <- ev_rec_dp_3.
  destruct Hs as [Hg _]. exact (Hg _ (tg_rec_dp_in 3 ltac:(lia))).
Qed.

Definition E0 (a : Assignment) : Z :=
  (dc a 0 * dc a 8) - (dc a 12 * dc a 4) - 1 - cc a 0 * 18446744073709551616.
Definition E1 (a : Assignment) : Z :=
  (dc a 0 * dc a 9 + dc a 1 * dc a 8) - (dc a 12 * dc a 5 + dc a 13 * dc a 4) + cc a 0 - cc a 1 * 18446744073709551616.
Definition E2 (a : Assignment) : Z :=
  (dc a 0 * dc a 10 + dc a 1 * dc a 9 + dc a 2 * dc a 8) - (dc a 12 * dc a 6 + dc a 13 * dc a 5 + dc a 14 * dc a 4) + cc a 1 - cc a 2 * 18446744073709551616.
Definition E3 (a : Assignment) : Z :=
  (dc a 0 * dc a 11 + dc a 1 * dc a 10 + dc a 2 * dc a 9 + dc a 3 * dc a 8) - (dc a 12 * dc a 7 + dc a 13 * dc a 6 + dc a 14 * dc a 5 + dc a 15 * dc a 4) + cc a 2 - cc a 3 * 18446744073709551616.
Definition E4 (a : Assignment) : Z :=
  (dc a 1 * dc a 11 + dc a 2 * dc a 10 + dc a 3 * dc a 9) - (dc a 13 * dc a 7 + dc a 14 * dc a 6 + dc a 15 * dc a 5 + dc a 16 * dc a 4) + cc a 3 - cc a 4 * 18446744073709551616.
Definition E5 (a : Assignment) : Z :=
  (dc a 2 * dc a 11 + dc a 3 * dc a 10) - (dc a 14 * dc a 7 + dc a 15 * dc a 6 + dc a 16 * dc a 5 + dc a 17 * dc a 4) + cc a 4 - cc a 5 * 18446744073709551616.
Definition E6 (a : Assignment) : Z :=
  (dc a 3 * dc a 11) - (dc a 15 * dc a 7 + dc a 16 * dc a 6 + dc a 17 * dc a 5 + dc a 18 * dc a 4) + cc a 5 - cc a 6 * 18446744073709551616.
Definition E7 (a : Assignment) : Z :=
  (0) - (dc a 16 * dc a 7 + dc a 17 * dc a 6 + dc a 18 * dc a 5 + dc a 19 * dc a 4) + cc a 6 - cc a 7 * 18446744073709551616.
Definition E8 (a : Assignment) : Z :=
  (0) - (dc a 17 * dc a 7 + dc a 18 * dc a 6 + dc a 19 * dc a 5) + cc a 7 - cc a 8 * 18446744073709551616.
Definition E9 (a : Assignment) : Z :=
  (0) - (dc a 18 * dc a 7 + dc a 19 * dc a 6) + cc a 8 - cc a 9 * 18446744073709551616.
Definition E10 (a : Assignment) : Z :=
  (0) - (dc a 19 * dc a 7) + cc a 9.
Definition R0 (a : Assignment) : Z :=
  (a (0%nat, 0%nat) * a (8%nat, 0%nat)) - (a (12%nat, 0%nat) * a (4%nat, 0%nat)) - 1 - a (20%nat, 0%nat) * 18446744073709551616.
Definition R1 (a : Assignment) : Z :=
  (a (0%nat, 0%nat) * a (9%nat, 0%nat) + a (1%nat, 0%nat) * a (8%nat, 0%nat)) - (a (12%nat, 0%nat) * a (5%nat, 0%nat) + a (13%nat, 0%nat) * a (4%nat, 0%nat)) + a (20%nat, 0%nat) - a (21%nat, 0%nat) * 18446744073709551616.
Definition R2 (a : Assignment) : Z :=
  (a (0%nat, 0%nat) * a (10%nat, 0%nat) + a (1%nat, 0%nat) * a (9%nat, 0%nat) + a (2%nat, 0%nat) * a (8%nat, 0%nat)) - (a (12%nat, 0%nat) * a (6%nat, 0%nat) + a (13%nat, 0%nat) * a (5%nat, 0%nat) + a (14%nat, 0%nat) * a (4%nat, 0%nat)) + a (21%nat, 0%nat) - a (22%nat, 0%nat) * 18446744073709551616.
Definition R3 (a : Assignment) : Z :=
  (a (0%nat, 0%nat) * a (11%nat, 0%nat) + a (1%nat, 0%nat) * a (10%nat, 0%nat) + a (2%nat, 0%nat) * a (9%nat, 0%nat) + a (3%nat, 0%nat) * a (8%nat, 0%nat)) - (a (12%nat, 0%nat) * a (7%nat, 0%nat) + a (13%nat, 0%nat) * a (6%nat, 0%nat) + a (14%nat, 0%nat) * a (5%nat, 0%nat) + a (15%nat, 0%nat) * a (4%nat, 0%nat)) + a (22%nat, 0%nat) - a (23%nat, 0%nat) * 18446744073709551616.
Definition R4 (a : Assignment) : Z :=
  (a (1%nat, 0%nat) * a (11%nat, 0%nat) + a (2%nat, 0%nat) * a (10%nat, 0%nat) + a (3%nat, 0%nat) * a (9%nat, 0%nat)) - (a (13%nat, 0%nat) * a (7%nat, 0%nat) + a (14%nat, 0%nat) * a (6%nat, 0%nat) + a (15%nat, 0%nat) * a (5%nat, 0%nat) + a (16%nat, 0%nat) * a (4%nat, 0%nat)) + a (23%nat, 0%nat) - a (24%nat, 0%nat) * 18446744073709551616.
Definition R5 (a : Assignment) : Z :=
  (a (2%nat, 0%nat) * a (11%nat, 0%nat) + a (3%nat, 0%nat) * a (10%nat, 0%nat)) - (a (14%nat, 0%nat) * a (7%nat, 0%nat) + a (15%nat, 0%nat) * a (6%nat, 0%nat) + a (16%nat, 0%nat) * a (5%nat, 0%nat) + a (17%nat, 0%nat) * a (4%nat, 0%nat)) + a (24%nat, 0%nat) - a (25%nat, 0%nat) * 18446744073709551616.
Definition R6 (a : Assignment) : Z :=
  (a (3%nat, 0%nat) * a (11%nat, 0%nat)) - (a (15%nat, 0%nat) * a (7%nat, 0%nat) + a (16%nat, 0%nat) * a (6%nat, 0%nat) + a (17%nat, 0%nat) * a (5%nat, 0%nat) + a (18%nat, 0%nat) * a (4%nat, 0%nat)) + a (25%nat, 0%nat) - a (26%nat, 0%nat) * 18446744073709551616.
Definition R7 (a : Assignment) : Z :=
  (0) - (a (16%nat, 0%nat) * a (7%nat, 0%nat) + a (17%nat, 0%nat) * a (6%nat, 0%nat) + a (18%nat, 0%nat) * a (5%nat, 0%nat) + a (19%nat, 0%nat) * a (4%nat, 0%nat)) + a (26%nat, 0%nat) - a (27%nat, 0%nat) * 18446744073709551616.
Definition R8 (a : Assignment) : Z :=
  (0) - (a (17%nat, 0%nat) * a (7%nat, 0%nat) + a (18%nat, 0%nat) * a (6%nat, 0%nat) + a (19%nat, 0%nat) * a (5%nat, 0%nat)) + a (27%nat, 0%nat) - a (28%nat, 0%nat) * 18446744073709551616.
Definition R9 (a : Assignment) : Z :=
  (0) - (a (18%nat, 0%nat) * a (7%nat, 0%nat) + a (19%nat, 0%nat) * a (6%nat, 0%nat)) + a (28%nat, 0%nat) - a (29%nat, 0%nat) * 18446744073709551616.
Definition R10 (a : Assignment) : Z :=
  (0) - (a (19%nat, 0%nat) * a (7%nat, 0%nat)) + a (29%nat, 0%nat).

Definition P0 (a : Assignment) : Z :=
  dc a 30 - dc a 4 + 2 - dc a 1748 * 18446744073709551616.
Definition P1 (a : Assignment) : Z :=
  dc a 31 - dc a 5 + dc a 1748 - dc a 1749 * 18446744073709551616.
Definition P2 (a : Assignment) : Z :=
  dc a 32 - dc a 6 + dc a 1749 - dc a 1750 * 18446744073709551616.
Definition P3 (a : Assignment) : Z :=
  dc a 33 - dc a 7 + dc a 1750.
Definition PR0 (a : Assignment) : Z :=
  a (30%nat, 0%nat) - a (4%nat, 0%nat) + 2 - a (1748%nat, 0%nat) * 18446744073709551616.
Definition PR1 (a : Assignment) : Z :=
  a (31%nat, 0%nat) - a (5%nat, 0%nat) + a (1748%nat, 0%nat) - a (1749%nat, 0%nat) * 18446744073709551616.
Definition PR2 (a : Assignment) : Z :=
  a (32%nat, 0%nat) - a (6%nat, 0%nat) + a (1749%nat, 0%nat) - a (1750%nat, 0%nat) * 18446744073709551616.
Definition PR3 (a : Assignment) : Z :=
  a (33%nat, 0%nat) - a (7%nat, 0%nat) + a (1750%nat, 0%nat).

Lemma ev_chain_0 : forall a, eval a (nth 0 tg_chain (EConst 0)) = R0 a.
Proof. intro a. unfold R0. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_1 : forall a, eval a (nth 1 tg_chain (EConst 0)) = R1 a.
Proof. intro a. unfold R1. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_2 : forall a, eval a (nth 2 tg_chain (EConst 0)) = R2 a.
Proof. intro a. unfold R2. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_3 : forall a, eval a (nth 3 tg_chain (EConst 0)) = R3 a.
Proof. intro a. unfold R3. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_4 : forall a, eval a (nth 4 tg_chain (EConst 0)) = R4 a.
Proof. intro a. unfold R4. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_5 : forall a, eval a (nth 5 tg_chain (EConst 0)) = R5 a.
Proof. intro a. unfold R5. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_6 : forall a, eval a (nth 6 tg_chain (EConst 0)) = R6 a.
Proof. intro a. unfold R6. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_7 : forall a, eval a (nth 7 tg_chain (EConst 0)) = R7 a.
Proof. intro a. unfold R7. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_8 : forall a, eval a (nth 8 tg_chain (EConst 0)) = R8 a.
Proof. intro a. unfold R8. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_9 : forall a, eval a (nth 9 tg_chain (EConst 0)) = R9 a.
Proof. intro a. unfold R9. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_chain_10 : forall a, eval a (nth 10 tg_chain (EConst 0)) = R10 a.
Proof. intro a. unfold R10. cbn [nth tg_chain eval]. ring. Qed.
Lemma ev_pchain_0 : forall a, eval a (nth 0 tg_pchain (EConst 0)) = PR0 a.
Proof. intro a. unfold PR0. cbn [nth tg_pchain eval]. ring. Qed.
Lemma ev_pchain_1 : forall a, eval a (nth 1 tg_pchain (EConst 0)) = PR1 a.
Proof. intro a. unfold PR1. cbn [nth tg_pchain eval]. ring. Qed.
Lemma ev_pchain_2 : forall a, eval a (nth 2 tg_pchain (EConst 0)) = PR2 a.
Proof. intro a. unfold PR2. cbn [nth tg_pchain eval]. ring. Qed.
Lemma ev_pchain_3 : forall a, eval a (nth 3 tg_pchain (EConst 0)) = PR3 a.
Proof. intro a. unfold PR3. cbn [nth tg_pchain eval]. ring. Qed.

Lemma cong_E0 : forall a, (E0 a) mod p = (R0 a) mod p.
Proof. intro a. unfold E0, R0. cong. Qed.
Lemma cong_E1 : forall a, (E1 a) mod p = (R1 a) mod p.
Proof. intro a. unfold E1, R1. cong. Qed.
Lemma cong_E2 : forall a, (E2 a) mod p = (R2 a) mod p.
Proof. intro a. unfold E2, R2. cong. Qed.
Lemma cong_E3 : forall a, (E3 a) mod p = (R3 a) mod p.
Proof. intro a. unfold E3, R3. cong. Qed.
Lemma cong_E4 : forall a, (E4 a) mod p = (R4 a) mod p.
Proof. intro a. unfold E4, R4. cong. Qed.
Lemma cong_E5 : forall a, (E5 a) mod p = (R5 a) mod p.
Proof. intro a. unfold E5, R5. cong. Qed.
Lemma cong_E6 : forall a, (E6 a) mod p = (R6 a) mod p.
Proof. intro a. unfold E6, R6. cong. Qed.
Lemma cong_E7 : forall a, (E7 a) mod p = (R7 a) mod p.
Proof. intro a. unfold E7, R7. cong. Qed.
Lemma cong_E8 : forall a, (E8 a) mod p = (R8 a) mod p.
Proof. intro a. unfold E8, R8. cong. Qed.
Lemma cong_E9 : forall a, (E9 a) mod p = (R9 a) mod p.
Proof. intro a. unfold E9, R9. cong. Qed.
Lemma cong_E10 : forall a, (E10 a) mod p = (R10 a) mod p.
Proof. intro a. unfold E10, R10. cong. Qed.
Lemma cong_P0 : forall a, (P0 a) mod p = (PR0 a) mod p.
Proof. intro a. unfold P0, PR0. cong. Qed.
Lemma cong_P1 : forall a, (P1 a) mod p = (PR1 a) mod p.
Proof. intro a. unfold P1, PR1. cong. Qed.
Lemma cong_P2 : forall a, (P2 a) mod p = (PR2 a) mod p.
Proof. intro a. unfold P2, PR2. cong. Qed.
Lemma cong_P3 : forall a, (P3 a) mod p = (PR3 a) mod p.
Proof. intro a. unfold P3, PR3. cong. Qed.

Definition BOUNDS (a : Assignment) : Prop :=
  (forall c, (c < 20)%nat -> 0 <= dc a c < 18446744073709551616)
  /\ (forall c, (30 <= c < 34)%nat -> 0 <= dc a c < 18446744073709551616)
  /\ (forall m, (m < 10)%nat -> - 295147905179352825856 <= cc a m < 295147905179352825856)
  /\ (forall c, (1748 <= c < 1751)%nat -> dc a c = 0 \/ dc a c = 1).

Lemma prod_bound : forall x y, 0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  0 <= x * y < 340282366920938463463374607431768211456.
Proof. intros. nia. Qed.

Lemma E0_zero : forall a, sat deployed_model a -> BOUNDS a -> E0 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E0, <- ev_chain_0.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 0%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 0) (dc a 8) (Hv 0%nat ltac:(lia)) (Hv 8%nat ltac:(lia))).
    pose proof (prod_bound (dc a 12) (dc a 4) (Hv 12%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 0%nat ltac:(lia)).
    unfold E0, HEADROOM. lia.
Qed.
Lemma E1_zero : forall a, sat deployed_model a -> BOUNDS a -> E1 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E1, <- ev_chain_1.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 1%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 0) (dc a 9) (Hv 0%nat ltac:(lia)) (Hv 9%nat ltac:(lia))).
    pose proof (prod_bound (dc a 1) (dc a 8) (Hv 1%nat ltac:(lia)) (Hv 8%nat ltac:(lia))).
    pose proof (prod_bound (dc a 12) (dc a 5) (Hv 12%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 13) (dc a 4) (Hv 13%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 0%nat ltac:(lia)).
    pose proof (Hc 1%nat ltac:(lia)).
    unfold E1, HEADROOM. lia.
Qed.
Lemma E2_zero : forall a, sat deployed_model a -> BOUNDS a -> E2 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E2, <- ev_chain_2.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 2%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 0) (dc a 10) (Hv 0%nat ltac:(lia)) (Hv 10%nat ltac:(lia))).
    pose proof (prod_bound (dc a 1) (dc a 9) (Hv 1%nat ltac:(lia)) (Hv 9%nat ltac:(lia))).
    pose proof (prod_bound (dc a 2) (dc a 8) (Hv 2%nat ltac:(lia)) (Hv 8%nat ltac:(lia))).
    pose proof (prod_bound (dc a 12) (dc a 6) (Hv 12%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 13) (dc a 5) (Hv 13%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 14) (dc a 4) (Hv 14%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 1%nat ltac:(lia)).
    pose proof (Hc 2%nat ltac:(lia)).
    unfold E2, HEADROOM. lia.
Qed.
Lemma E3_zero : forall a, sat deployed_model a -> BOUNDS a -> E3 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E3, <- ev_chain_3.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 3%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 0) (dc a 11) (Hv 0%nat ltac:(lia)) (Hv 11%nat ltac:(lia))).
    pose proof (prod_bound (dc a 1) (dc a 10) (Hv 1%nat ltac:(lia)) (Hv 10%nat ltac:(lia))).
    pose proof (prod_bound (dc a 2) (dc a 9) (Hv 2%nat ltac:(lia)) (Hv 9%nat ltac:(lia))).
    pose proof (prod_bound (dc a 3) (dc a 8) (Hv 3%nat ltac:(lia)) (Hv 8%nat ltac:(lia))).
    pose proof (prod_bound (dc a 12) (dc a 7) (Hv 12%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 13) (dc a 6) (Hv 13%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 14) (dc a 5) (Hv 14%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 15) (dc a 4) (Hv 15%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 2%nat ltac:(lia)).
    pose proof (Hc 3%nat ltac:(lia)).
    unfold E3, HEADROOM. lia.
Qed.
Lemma E4_zero : forall a, sat deployed_model a -> BOUNDS a -> E4 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E4, <- ev_chain_4.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 4%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 1) (dc a 11) (Hv 1%nat ltac:(lia)) (Hv 11%nat ltac:(lia))).
    pose proof (prod_bound (dc a 2) (dc a 10) (Hv 2%nat ltac:(lia)) (Hv 10%nat ltac:(lia))).
    pose proof (prod_bound (dc a 3) (dc a 9) (Hv 3%nat ltac:(lia)) (Hv 9%nat ltac:(lia))).
    pose proof (prod_bound (dc a 13) (dc a 7) (Hv 13%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 14) (dc a 6) (Hv 14%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 15) (dc a 5) (Hv 15%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 16) (dc a 4) (Hv 16%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 3%nat ltac:(lia)).
    pose proof (Hc 4%nat ltac:(lia)).
    unfold E4, HEADROOM. lia.
Qed.
Lemma E5_zero : forall a, sat deployed_model a -> BOUNDS a -> E5 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E5, <- ev_chain_5.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 5%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 2) (dc a 11) (Hv 2%nat ltac:(lia)) (Hv 11%nat ltac:(lia))).
    pose proof (prod_bound (dc a 3) (dc a 10) (Hv 3%nat ltac:(lia)) (Hv 10%nat ltac:(lia))).
    pose proof (prod_bound (dc a 14) (dc a 7) (Hv 14%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 15) (dc a 6) (Hv 15%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 16) (dc a 5) (Hv 16%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 17) (dc a 4) (Hv 17%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 4%nat ltac:(lia)).
    pose proof (Hc 5%nat ltac:(lia)).
    unfold E5, HEADROOM. lia.
Qed.
Lemma E6_zero : forall a, sat deployed_model a -> BOUNDS a -> E6 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E6, <- ev_chain_6.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 6%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 3) (dc a 11) (Hv 3%nat ltac:(lia)) (Hv 11%nat ltac:(lia))).
    pose proof (prod_bound (dc a 15) (dc a 7) (Hv 15%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 16) (dc a 6) (Hv 16%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 17) (dc a 5) (Hv 17%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 18) (dc a 4) (Hv 18%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 5%nat ltac:(lia)).
    pose proof (Hc 6%nat ltac:(lia)).
    unfold E6, HEADROOM. lia.
Qed.
Lemma E7_zero : forall a, sat deployed_model a -> BOUNDS a -> E7 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E7, <- ev_chain_7.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 7%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 16) (dc a 7) (Hv 16%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 17) (dc a 6) (Hv 17%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 18) (dc a 5) (Hv 18%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (prod_bound (dc a 19) (dc a 4) (Hv 19%nat ltac:(lia)) (Hv 4%nat ltac:(lia))).
    pose proof (Hc 6%nat ltac:(lia)).
    pose proof (Hc 7%nat ltac:(lia)).
    unfold E7, HEADROOM. lia.
Qed.
Lemma E8_zero : forall a, sat deployed_model a -> BOUNDS a -> E8 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E8, <- ev_chain_8.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 8%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 17) (dc a 7) (Hv 17%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 18) (dc a 6) (Hv 18%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (prod_bound (dc a 19) (dc a 5) (Hv 19%nat ltac:(lia)) (Hv 5%nat ltac:(lia))).
    pose proof (Hc 7%nat ltac:(lia)).
    pose proof (Hc 8%nat ltac:(lia)).
    unfold E8, HEADROOM. lia.
Qed.
Lemma E9_zero : forall a, sat deployed_model a -> BOUNDS a -> E9 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E9, <- ev_chain_9.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 9%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 18) (dc a 7) (Hv 18%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (prod_bound (dc a 19) (dc a 6) (Hv 19%nat ltac:(lia)) (Hv 6%nat ltac:(lia))).
    pose proof (Hc 8%nat ltac:(lia)).
    pose proof (Hc 9%nat ltac:(lia)).
    unfold E9, HEADROOM. lia.
Qed.
Lemma E10_zero : forall a, sat deployed_model a -> BOUNDS a -> E10 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_E10, <- ev_chain_10.
    destruct Hs as [Hg _]. exact (Hg _ (tg_chain_in 10%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (prod_bound (dc a 19) (dc a 7) (Hv 19%nat ltac:(lia)) (Hv 7%nat ltac:(lia))).
    pose proof (Hc 9%nat ltac:(lia)).
    unfold E10, HEADROOM. lia.
Qed.

Lemma P0_zero : forall a, sat deployed_model a -> BOUNDS a -> P0 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_P0, <- ev_pchain_0.
    destruct Hs as [Hg _]. exact (Hg _ (tg_pchain_in 0%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (Hd 30%nat ltac:(lia)). pose proof (Hv 4%nat ltac:(lia)).
    pose proof (Hb 1748%nat ltac:(lia)).
    unfold P0, HEADROOM. lia.
Qed.
Lemma P1_zero : forall a, sat deployed_model a -> BOUNDS a -> P1 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_P1, <- ev_pchain_1.
    destruct Hs as [Hg _]. exact (Hg _ (tg_pchain_in 1%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (Hd 31%nat ltac:(lia)). pose proof (Hv 5%nat ltac:(lia)).
    pose proof (Hb 1748%nat ltac:(lia)).
    pose proof (Hb 1749%nat ltac:(lia)).
    unfold P1, HEADROOM. lia.
Qed.
Lemma P2_zero : forall a, sat deployed_model a -> BOUNDS a -> P2 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_P2, <- ev_pchain_2.
    destruct Hs as [Hg _]. exact (Hg _ (tg_pchain_in 2%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (Hd 32%nat ltac:(lia)). pose proof (Hv 6%nat ltac:(lia)).
    pose proof (Hb 1749%nat ltac:(lia)).
    pose proof (Hb 1750%nat ltac:(lia)).
    unfold P2, HEADROOM. lia.
Qed.
Lemma P3_zero : forall a, sat deployed_model a -> BOUNDS a -> P3 a = 0.
Proof.
  intros a Hs HB. apply small_residue_is_zero.
  - rewrite cong_P3, <- ev_pchain_3.
    destruct Hs as [Hg _]. exact (Hg _ (tg_pchain_in 3%nat ltac:(lia))).
  - destruct HB as [Hv [Hd [Hc Hb]]].
    pose proof (Hd 33%nat ltac:(lia)). pose proof (Hv 7%nat ltac:(lia)).
    pose proof (Hb 1750%nat ltac:(lia)).
    unfold P3, HEADROOM. lia.
Qed.

Definition VALI (a : Assignment) : Z := dc a 0 + 18446744073709551616 * dc a 1 + 340282366920938463463374607431768211456 * dc a 2 + 6277101735386680763835789423207666416102355444464034512896 * dc a 3.
Definition VALP (a : Assignment) : Z := dc a 4 + 18446744073709551616 * dc a 5 + 340282366920938463463374607431768211456 * dc a 6 + 6277101735386680763835789423207666416102355444464034512896 * dc a 7.
Definition VALO (a : Assignment) : Z := dc a 8 + 18446744073709551616 * dc a 9 + 340282366920938463463374607431768211456 * dc a 10 + 6277101735386680763835789423207666416102355444464034512896 * dc a 11.
Definition VALQ (a : Assignment) : Z := dc a 12 + 18446744073709551616 * dc a 13 + 340282366920938463463374607431768211456 * dc a 14 + 6277101735386680763835789423207666416102355444464034512896 * dc a 15 + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * dc a 16 + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 * dc a 17 + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 * dc a 18 + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656 * dc a 19.
Definition VALDP (a : Assignment) : Z := dc a 30 + 18446744073709551616 * dc a 31 + 340282366920938463463374607431768211456 * dc a 32 + 6277101735386680763835789423207666416102355444464034512896 * dc a 33.

Lemma chain_telescopes : forall a,
  E0 a + 18446744073709551616 * E1 a + 340282366920938463463374607431768211456 * E2 a + 6277101735386680763835789423207666416102355444464034512896 * E3 a + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * E4 a + 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936576 * E5 a + 39402006196394479212279040100143613805079739270465446667948293404245721771497210611414266254884915640806627990306816 * E6 a + 726838724295606890549323807888004534353641360687318060281490199180639288113397923326191050713763565560762521606266177933534601628614656 * E7 a + 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 * E8 a + 247330401473104534060502521019647190035131349101211839914063056092897225106531867170316401061243044989597671426016139339351365034306751209967546155101893167916606772148699136 * E9 a + 4562440617622195218641171605700291324893228507248559930579192517899275167208677386505912811317371399778642309573594407310688704721375437998252661319722214188251994674360264950082874192246603776 * E10 a
  = VALI a * VALO a - VALQ a * VALP a - 1.
Proof.
  intro a. unfold E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, VALI, VALO, VALQ, VALP. ring.
Qed.

Lemma comparator_telescopes : forall a,
  P0 a + 18446744073709551616 * P1 a + 340282366920938463463374607431768211456 * P2 a + 6277101735386680763835789423207666416102355444464034512896 * P3 a = VALDP a - VALP a + 2.
Proof.
  intro a. unfold P0, P1, P2, P3, VALDP, VALP. ring.
Qed.

Theorem euclidean_identity : forall a,
  sat deployed_model a -> BOUNDS a ->
  VALI a * VALO a = VALQ a * VALP a + 1.
Proof.
  intros a Hs HB. pose proof (chain_telescopes a) as T.
  rewrite (E0_zero a Hs HB) in T.
  rewrite (E1_zero a Hs HB) in T.
  rewrite (E2_zero a Hs HB) in T.
  rewrite (E3_zero a Hs HB) in T.
  rewrite (E4_zero a Hs HB) in T.
  rewrite (E5_zero a Hs HB) in T.
  rewrite (E6_zero a Hs HB) in T.
  rewrite (E7_zero a Hs HB) in T.
  rewrite (E8_zero a Hs HB) in T.
  rewrite (E9_zero a Hs HB) in T.
  rewrite (E10_zero a Hs HB) in T.
  lia.
Qed.

(* The comparator: for an accepted filling that satisfies BOUNDS, which bridge_sound derives from
   acceptance together with the input assumption (bounds_hold), the value of p is 2 more than the
   value of four in-range limbs. *)
Theorem comparator_forces_the_modulus : forall a,
  sat deployed_model a -> BOUNDS a -> VALP a = VALDP a + 2.
Proof.
  intros a Hs HB. pose proof (comparator_telescopes a) as T.
  rewrite (P0_zero a Hs HB) in T.
  rewrite (P1_zero a Hs HB) in T.
  rewrite (P2_zero a Hs HB) in T.
  rewrite (P3_zero a Hs HB) in T.
  lia.
Qed.

Theorem modulus_exceeds_one : forall a,
  sat deployed_model a -> BOUNDS a -> 1 < VALP a.
Proof.
  intros a Hs HB. pose proof (comparator_forces_the_modulus a Hs HB) as T.
  destruct HB as [_ [Hd _]].
  pose proof (Hd 30%nat ltac:(lia)).
  pose proof (Hd 31%nat ltac:(lia)).
  pose proof (Hd 32%nat ltac:(lia)).
  pose proof (Hd 33%nat ltac:(lia)).
  unfold VALDP in T. lia.
Qed.

Lemma pre_inp_bound : forall a, bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
  forall i, (i < 4)%nat -> 0 <= dc a (0 + i)%nat < 18446744073709551616.
Proof.
  intros a [_ [_ [Hi _]]] i Hii.
  pose proof (Hi i ltac:(unfold bmi_rule.K; lia)) as H.
  rewrite (inp_l_nth a i Hii), bmi_rule.B_value in H. exact H.
Qed.
Lemma pre_p_bound : forall a, bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
  forall i, (i < 4)%nat -> 0 <= dc a (4 + i)%nat < 18446744073709551616.
Proof.
  intros a [_ [_ [_ Hp]]] i Hii.
  pose proof (Hp i ltac:(unfold bmi_rule.K; lia)) as H.
  rewrite (p_l_nth a i Hii), bmi_rule.B_value in H. exact H.
Qed.

Lemma bounds_hold : forall a,
  sat deployed_model a -> bmi_rule.PRE_bmi (inp_l a) (p_l a) -> BOUNDS a.
Proof.
  intros a Hs Hpre.
  pose proof (pre_inp_bound a Hpre) as Hin.
  pose proof (pre_p_bound a Hpre) as Hpp.
  split; [ | split; [ | split ] ].
  - intros c Hc.
    destruct c as [|c]; [ exact (Hin 0%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hin 1%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hin 2%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hin 3%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hpp 0%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hpp 1%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hpp 2%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (Hpp 3%nat ltac:(lia)) | ].
    destruct c as [|c]; [ exact (rng_out_0 a Hs) | ].
    destruct c as [|c]; [ exact (rng_out_1 a Hs) | ].
    destruct c as [|c]; [ exact (rng_out_2 a Hs) | ].
    destruct c as [|c]; [ exact (rng_out_3 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_0 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_1 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_2 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_3 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_4 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_5 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_6 a Hs) | ].
    destruct c as [|c]; [ exact (rng_q_7 a Hs) | ].
    lia.
  - intros c Hc.
    destruct Hc as [Hlo Hhi].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].
    destruct c as [|c]; [ lia | ].

    destruct c as [|c]; [ exact (rng_dp_0 a Hs) | ].
    destruct c as [|c]; [ exact (rng_dp_1 a Hs) | ].
    destruct c as [|c]; [ exact (rng_dp_2 a Hs) | ].
    destruct c as [|c]; [ exact (rng_dp_3 a Hs) | ].
    lia.
  - intros m Hm. unfold cc.
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_0 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_1 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_2 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_3 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_4 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_5 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_6 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_7 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_8 a Hs); lia | ].
    destruct m as [|m]; [ cbn [Nat.add]; pose proof (rng_c_9 a Hs); lia | ].
    lia.
  - intros c Hc. destruct Hc as [Hlo Hhi]. unfold dc.
    assert (Hj : (c - 34 < 1717)%nat) by lia.
    pose proof (every_bit_cell_is_boolean a Hs (c - 34)%nat Hj) as H.
    replace (34 + (c - 34))%nat with c in H by lia. exact H.
Qed.

Lemma VAL_inp_l : forall a, bmi_rule.VAL (inp_l a) = VALI a.
Proof. intro a. unfold bmi_rule.VAL, inp_l, VALI. cbn [fold_right]. rewrite bmi_rule.B_value. ring. Qed.
Lemma VAL_p_l : forall a, bmi_rule.VAL (p_l a) = VALP a.
Proof. intro a. unfold bmi_rule.VAL, p_l, VALP. cbn [fold_right]. rewrite bmi_rule.B_value. ring. Qed.
Lemma VAL_out_l : forall a, bmi_rule.VAL (out_l a) = VALO a.
Proof. intro a. unfold bmi_rule.VAL, out_l, VALO. cbn [fold_right]. rewrite bmi_rule.B_value. ring. Qed.

Lemma out_limbs_in_range : forall a,
  sat deployed_model a -> bmi_rule.limbs_in_range (out_l a).
Proof.
  intros a Hs i Hi. rewrite (out_l_nth a i ltac:(unfold bmi_rule.K in Hi; lia)).
  rewrite bmi_rule.B_value.
  unfold bmi_rule.K in Hi.
  destruct i as [|i]; [ exact (rng_out_0 a Hs) | ].
  destruct i as [|i]; [ exact (rng_out_1 a Hs) | ].
  destruct i as [|i]; [ exact (rng_out_2 a Hs) | ].
  destruct i as [|i]; [ exact (rng_out_3 a Hs) | ].
  lia.
Qed.

(* Soundness. *)
Theorem bridge_sound : forall a,
  sat deployed_model a ->
  CANON_bmi a ->
  bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
  bmi_rule.REL_bmi (inp_l a) (p_l a) (out_l a).
Proof.
  intros a Hs Hcan Hpre.
  pose proof (bounds_hold a Hs Hpre) as HB.

  pose proof (modulus_exceeds_one a Hs HB) as Hmodv.
  split; [ exact (out_l_length a) | ].
  split; [ exact (out_limbs_in_range a Hs) | ].
  split; [ rewrite VAL_p_l; exact Hmodv | ].

  pose proof (euclidean_identity a Hs HB) as HE.
  rewrite VAL_inp_l, VAL_out_l, VAL_p_l, HE, Z.add_comm.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Theorem bridge_sound_R : forall a,
  sat deployed_model a -> CANON_bmi a ->
  bmi_rule.R_bmi (inp_l a) (p_l a) (out_l a).
Proof.
  intros a Hs Hcan Hpre. exact (bridge_sound a Hs Hcan Hpre).
Qed.

Theorem the_modulus_conjunct_is_now_ENFORCED : forall a,
  sat deployed_model a ->
  bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
  1 < bmi_rule.VAL (p_l a).
Proof.
  intros a Hs Hpre. rewrite VAL_p_l.
  exact (modulus_exceeds_one a Hs (bounds_hold a Hs Hpre)).
Qed.

Theorem nonvacuity_the_honest_row_decodes_to_the_anchor :
  sat deployed_model wit_honest_bmi
  /\ inp_l wit_honest_bmi = bmi_rule.INP_ANCHOR
  /\ p_l   wit_honest_bmi = bmi_rule.P_ANCHOR
  /\ out_l wit_honest_bmi = bmi_rule.OUT_ANCHOR.
Proof.
  split; [ exact honest_full_sat_bmi | ].
  split; [ | split ];
  unfold inp_l, p_l, out_l, dc, bmi_rule.INP_ANCHOR, bmi_rule.P_ANCHOR,
         bmi_rule.OUT_ANCHOR;
  vm_compute; reflexivity.
Qed.

Theorem nonvacuity_a_real_inverse_is_ACCEPTED :
  bmi_rule.REL_bmi (inp_l wit_honest_bmi) (p_l wit_honest_bmi)
                   (out_l wit_honest_bmi).
Proof.
  destruct nonvacuity_the_honest_row_decodes_to_the_anchor as [Hs [Hi [Hp Ho]]].
  apply bridge_sound; [ exact Hs | apply CANON_is_free | ].
  rewrite Hi, Hp. exact bmi_rule.anchor_pre.
Qed.

Theorem no_satisfying_row_has_a_degenerate_modulus : forall a,
  sat deployed_model a ->
  bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
  bmi_rule.VAL (p_l a) <> 0 /\ bmi_rule.VAL (p_l a) <> 1.
Proof.
  intros a Hs Hpre.
  pose proof (the_modulus_conjunct_is_now_ENFORCED a Hs Hpre). lia.
Qed.

Theorem the_comparator_does_not_make_out_unique : forall a out',
  sat deployed_model a ->
  bmi_rule.PRE_bmi (inp_l a) (p_l a) ->
  length out' = bmi_rule.K ->
  bmi_rule.limbs_in_range out' ->
  bmi_rule.VAL out' = bmi_rule.VAL (out_l a) + bmi_rule.VAL (p_l a) ->
  bmi_rule.REL_bmi (inp_l a) (p_l a) out'.
Proof.
  intros a out' Hs Hpre Hl Hr Hv.
  exact (bmi_rule.shifting_out_by_p_preserves_the_relation
           (inp_l a) (p_l a) (out_l a) out'
           (bridge_sound a Hs (CANON_is_free a) Hpre) Hl Hr Hv).
Qed.

Print Assumptions nonvacuity_the_honest_row_decodes_to_the_anchor.
Print Assumptions nonvacuity_a_real_inverse_is_ACCEPTED.
Print Assumptions no_satisfying_row_has_a_degenerate_modulus.
Print Assumptions the_comparator_does_not_make_out_unique.

Print Assumptions bridge_sound.
Print Assumptions bridge_sound_R.
Print Assumptions the_modulus_conjunct_is_now_ENFORCED.
Print Assumptions euclidean_identity.
Print Assumptions comparator_forces_the_modulus.
Print Assumptions modulus_exceeds_one.
