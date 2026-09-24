(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Reading the operand triple off a filling: each operand cell as its canonical remainder modulo p (dc),
   the vectors inp_l, p_l and out_l, and the canonicity predicate CANON_bmi, which every filling
   satisfies (CANON_is_free). Also the public cells' agreement with the output cells, derived from the
   copy constraints (answer_pins_are_DERIVED), and the checked count of polynomial constraints (dg_len).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia List Znumtheory. Import ListNotations.
Open Scope Z_scope.

Require Import Generated.bmi_model_gen.
Require Import Generated.bmi_wires_gen.
Require Import Generated.bmi_scaffold_gen.
Require Import Constraints.field_order_lift.
Require Import Constraints.range_field_pasta.
Require bmi_rule.

Lemma p_eq_pasta : p = pasta_p.
Proof. reflexivity. Qed.

Lemma p_prime : prime p.
Proof. rewrite p_eq_pasta. exact pasta_prime. Qed.

Lemma p_ge2 : 2 <= p.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Definition HEADROOM : Z := 87112285931760246646623899502532662132736.

Lemma HEADROOM_is_2_136 : HEADROOM = 2 ^ 136.
Proof. unfold HEADROOM. vm_compute. reflexivity. Qed.

Lemma p_big : HEADROOM <= p.
Proof. unfold HEADROOM. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma small_residue_is_zero : forall x,
  x mod p = 0 -> - HEADROOM < x < HEADROOM -> x = 0.
Proof.
  intros x Hm Hb. pose proof p_big as Hp. pose proof p_ge2 as H2.
  apply Z.mod_divide in Hm; [| lia]. destruct Hm as [k Hk].
  destruct (Z.eq_dec k 0) as [->|Hk0]; [ lia | ].
  assert (1 <= Z.abs k) by lia.
  assert (Z.abs x = Z.abs k * p) by (rewrite Hk, Z.abs_mul, (Z.abs_eq p) by lia; reflexivity).
  nia.
Qed.

Definition dc (a : Assignment) (c : nat) : Z := (a (c, 0%nat)) mod p.

Definition INP_BASE   : nat := 0.
Definition P_BASE     : nat := 4.
Definition OUT_BASE   : nat := 8.
Definition Q_BASE     : nat := 12.
Definition C_BASE     : nat := 20.
Definition DP_BASE    : nat := 30.
Definition OUTBIT_BASE: nat := 34.
Definition QBIT_BASE  : nat := 290.
Definition CBIT_BASE  : nat := 802.
Definition DPBIT_BASE : nat := 1492.
Definition PCBIT_BASE : nat := 1748.

Definition KL   : nat := 4.
Definition QKL  : nat := 8.
Definition NCAR : nat := 10.
Definition NPOSI: nat := 11.
Definition NPC  : nat := 3.
Definition NB   : nat := 64.
Definition CB   : nat := 69.

Definition BASE : Z := 18446744073709551616.
Definition CSHIFT : Z := 295147905179352825856.

Lemma BASE_is_2_64 : BASE = 2 ^ 64. Proof. vm_compute. reflexivity. Qed.
Lemma CSHIFT_is_2_68 : CSHIFT = 2 ^ 68. Proof. vm_compute. reflexivity. Qed.

Definition inp_l (a : Assignment) : list Z :=
  [dc a 0; dc a 1; dc a 2; dc a 3].
Definition p_l (a : Assignment) : list Z :=
  [dc a 4; dc a 5; dc a 6; dc a 7].
Definition out_l (a : Assignment) : list Z :=
  [dc a 8; dc a 9; dc a 10; dc a 11].

Definition q_l (a : Assignment) : list Z :=
  [dc a 12; dc a 13; dc a 14; dc a 15; dc a 16; dc a 17; dc a 18; dc a 19].
Definition dp_l (a : Assignment) : list Z :=
  [dc a 30; dc a 31; dc a 32; dc a 33].

Definition cs (a : Assignment) (m : nat) : Z := (a ((C_BASE + m)%nat, 0%nat) + CSHIFT) mod p.

Lemma inp_l_length : forall a, length (inp_l a) = bmi_rule.K.
Proof. reflexivity. Qed.
Lemma p_l_length : forall a, length (p_l a) = bmi_rule.K.
Proof. reflexivity. Qed.
Lemma out_l_length : forall a, length (out_l a) = bmi_rule.K.
Proof. reflexivity. Qed.

Lemma out_l_nth : forall a i, (i < 4)%nat -> nth i (out_l a) 0 = dc a (8 + i).
Proof.
  intros a i Hi.
  do 4 (destruct i as [|i]; [ reflexivity | ]). lia.
Qed.
Lemma inp_l_nth : forall a i, (i < 4)%nat -> nth i (inp_l a) 0 = dc a (0 + i).
Proof.
  intros a i Hi.
  do 4 (destruct i as [|i]; [ reflexivity | ]). lia.
Qed.
Lemma p_l_nth : forall a i, (i < 4)%nat -> nth i (p_l a) 0 = dc a (4 + i).
Proof.
  intros a i Hi.
  do 4 (destruct i as [|i]; [ reflexivity | ]). lia.
Qed.
Lemma dp_l_nth : forall a i, (i < 4)%nat -> nth i (dp_l a) 0 = dc a (30 + i).
Proof.
  intros a i Hi.
  do 4 (destruct i as [|i]; [ reflexivity | ]). lia.
Qed.
Lemma q_l_nth : forall a i, (i < 8)%nat -> nth i (q_l a) 0 = dc a (12 + i).
Proof.
  intros a i Hi.
  do 8 (destruct i as [|i]; [ reflexivity | ]). lia.
Qed.

Definition bool_gate (c : nat) : Expr :=
  EMul (ECell (c, 0%nat)) (ESub (ECell (c, 0%nat)) (EConst 1)).

Lemma in_firstn_in : forall (A : Type) n (l : list A) x,
  In x (firstn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [ destruct H | ].
  destruct l as [|y l]; [ destruct H | ].
  cbn [firstn] in H. destruct H as [->|H]; [ left; reflexivity | ].
  right. exact (IH l x H).
Qed.

Lemma in_skipn_in : forall (A : Type) n (l : list A) x,
  In x (skipn n l) -> In x l.
Proof.
  intros A n. induction n as [|n IH]; intros l x H; [ exact H | ].
  destruct l as [|y l]; [ destruct H | ].
  cbn [skipn] in H. right. exact (IH l x H).
Qed.

Theorem head_is_the_booleanity_bank :
  firstn 1717 deployed_gates = map (fun j => bool_gate (34 + j)) (seq 0 1717).
Proof. vm_compute. reflexivity. Qed.

Lemma bool_gate_in_model : forall j, (j < 1717)%nat ->
  In (bool_gate (34 + j)) deployed_gates.
Proof.
  intros j Hj.
  apply (in_firstn_in _ 1717).
  rewrite head_is_the_booleanity_bank.
  apply (in_map (fun k => bool_gate (34 + k)%nat)). apply in_seq. lia.
Qed.

Definition tail_gates : list Expr :=
  Eval vm_compute in (skipn 1717 deployed_gates).

Lemma tail_gates_length : length tail_gates = 41%nat.
Proof. reflexivity. Qed.

(* The model has 1,758 polynomial constraints (the 4 copy constraints are separate). *)
Lemma dg_len : length deployed_gates = 1758%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma head_and_tail_exhaust_the_model :
  (1717 + length tail_gates)%nat = length deployed_gates.
Proof. rewrite tail_gates_length, dg_len. reflexivity. Qed.

Lemma tail_gate_in_model : forall k, (k < 41)%nat ->
  In (nth k tail_gates (EConst 0)) deployed_gates.
Proof.
  intros k Hk.
  apply (in_skipn_in _ 1717).
  change (skipn 1717 deployed_gates) with tail_gates.
  apply nth_In. rewrite tail_gates_length. exact Hk.
Qed.

Definition tg_rec_out : list Expr := Eval vm_compute in (firstn 4 tail_gates).
Definition tg_rec_q   : list Expr := Eval vm_compute in (firstn 8 (skipn 4 tail_gates)).
Definition tg_rec_c   : list Expr := Eval vm_compute in (firstn 10 (skipn 12 tail_gates)).
Definition tg_rec_dp  : list Expr := Eval vm_compute in (firstn 4 (skipn 22 tail_gates)).
Definition tg_chain   : list Expr := Eval vm_compute in (firstn 11 (skipn 26 tail_gates)).
Definition tg_pchain  : list Expr := Eval vm_compute in (skipn 37 tail_gates).

Lemma tg_rec_out_eq : tg_rec_out = firstn 4 tail_gates.
Proof. vm_compute. reflexivity. Qed.
Lemma tg_rec_q_eq : tg_rec_q = firstn 8 (skipn 4 tail_gates).
Proof. vm_compute. reflexivity. Qed.
Lemma tg_rec_c_eq : tg_rec_c = firstn 10 (skipn 12 tail_gates).
Proof. vm_compute. reflexivity. Qed.
Lemma tg_rec_dp_eq : tg_rec_dp = firstn 4 (skipn 22 tail_gates).
Proof. vm_compute. reflexivity. Qed.
Lemma tg_chain_eq : tg_chain = firstn 11 (skipn 26 tail_gates).
Proof. vm_compute. reflexivity. Qed.
Lemma tg_pchain_eq : tg_pchain = skipn 37 tail_gates.
Proof. vm_compute. reflexivity. Qed.

Theorem tail_split_is_a_partition :
  tg_rec_out ++ tg_rec_q ++ tg_rec_c ++ tg_rec_dp ++ tg_chain ++ tg_pchain
  = tail_gates.
Proof. vm_compute. reflexivity. Qed.

Lemma tg_rec_out_len : length tg_rec_out = 4%nat. Proof. reflexivity. Qed.
Lemma tg_rec_q_len   : length tg_rec_q   = 8%nat. Proof. reflexivity. Qed.
Lemma tg_rec_c_len   : length tg_rec_c   = 10%nat. Proof. reflexivity. Qed.
Lemma tg_rec_dp_len  : length tg_rec_dp  = 4%nat. Proof. reflexivity. Qed.
Lemma tg_chain_len   : length tg_chain   = 11%nat. Proof. reflexivity. Qed.
Lemma tg_pchain_len  : length tg_pchain  = 4%nat. Proof. reflexivity. Qed.

Lemma in_tail_in_model : forall x, In x tail_gates -> In x deployed_gates.
Proof.
  intros x H. apply (in_skipn_in _ 1717).
  change (skipn 1717 deployed_gates) with tail_gates. exact H.
Qed.

Lemma tg_rec_out_in : forall k, (k < 4)%nat ->
  In (nth k tg_rec_out (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model.
  apply (in_firstn_in _ 4). rewrite <- tg_rec_out_eq.
  apply nth_In. rewrite tg_rec_out_len. exact Hk.
Qed.
Lemma tg_rec_q_in : forall k, (k < 8)%nat ->
  In (nth k tg_rec_q (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 4).
  apply (in_firstn_in _ 8). rewrite <- tg_rec_q_eq.
  apply nth_In. rewrite tg_rec_q_len. exact Hk.
Qed.
Lemma tg_rec_c_in : forall k, (k < 10)%nat ->
  In (nth k tg_rec_c (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 12).
  apply (in_firstn_in _ 10). rewrite <- tg_rec_c_eq.
  apply nth_In. rewrite tg_rec_c_len. exact Hk.
Qed.
Lemma tg_rec_dp_in : forall k, (k < 4)%nat ->
  In (nth k tg_rec_dp (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 22).
  apply (in_firstn_in _ 4). rewrite <- tg_rec_dp_eq.
  apply nth_In. rewrite tg_rec_dp_len. exact Hk.
Qed.
Lemma tg_chain_in : forall k, (k < 11)%nat ->
  In (nth k tg_chain (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 26).
  apply (in_firstn_in _ 11). rewrite <- tg_chain_eq.
  apply nth_In. rewrite tg_chain_len. exact Hk.
Qed.
Lemma tg_pchain_in : forall k, (k < 4)%nat ->
  In (nth k tg_pchain (EConst 0)) deployed_gates.
Proof.
  intros k Hk. apply in_tail_in_model. apply (in_skipn_in _ 37).
  rewrite <- tg_pchain_eq.
  apply nth_In. rewrite tg_pchain_len. exact Hk.
Qed.

Definition CANON_bmi (a : Assignment) : Prop :=
  (forall i, (i < 4)%nat -> 0 <= dc a (0 + i) < p)
  /\ (forall i, (i < 4)%nat -> 0 <= dc a (4 + i) < p)
  /\ (forall i, (i < 4)%nat -> 0 <= dc a (8 + i) < p).

Theorem CANON_is_free : forall a, CANON_bmi a.
Proof.
  intro a. pose proof p_ge2 as H2.
  unfold CANON_bmi, dc.
  split; [ | split ]; intros k Hk; apply Z.mod_pos_bound; lia.
Qed.

Definition PINS_bmi (a : Assignment) : Prop :=
  dc a 8 = (a (4000%nat, 0%nat)) mod p
  /\ dc a 9 = (a (4000%nat, 1%nat)) mod p
  /\ dc a 10 = (a (4000%nat, 2%nat)) mod p
  /\ dc a 11 = (a (4000%nat, 3%nat)) mod p.

Theorem answer_pins_are_DERIVED : forall a,
  sat deployed_model a -> PINS_bmi a.
Proof.
  intros a Hsat. destruct Hsat as [_ Hc].
  unfold PINS_bmi, dc.
  repeat split.
  - exact (copy_get a _ _ Hc in_copy_1).
  - exact (copy_get a _ _ Hc in_copy_2).
  - exact (copy_get a _ _ Hc in_copy_3).
  - exact (copy_get a _ _ Hc in_copy_4).
Qed.

Theorem every_bit_cell_is_boolean : forall a,
  sat deployed_model a ->
  forall j, (j < 1717)%nat ->
    (a ((34 + j)%nat, 0%nat)) mod p = 0 \/ (a ((34 + j)%nat, 0%nat)) mod p = 1.
Proof.
  intros a [Hg _] j Hj.
  pose proof (Hg _ (bool_gate_in_model j Hj)) as H.
  unfold gate_holds in H. cbn [eval] in H.
  apply (range_field.bool_mod_forces_01 p p_prime).
  replace (a ((34 + j)%nat, 0%nat) * a ((34 + j)%nat, 0%nat) - a ((34 + j)%nat, 0%nat))
     with (a ((34 + j)%nat, 0%nat) * (a ((34 + j)%nat, 0%nat) - 1)) by ring.
  exact H.
Qed.

Print Assumptions p_prime.
Print Assumptions small_residue_is_zero.
Print Assumptions head_is_the_booleanity_bank.
Print Assumptions tail_gates_length.
Print Assumptions tail_gate_in_model.
Print Assumptions CANON_is_free.
Print Assumptions answer_pins_are_DERIVED.
Print Assumptions every_bit_cell_is_boolean.
Print Assumptions tail_split_is_a_partition.
Print Assumptions tg_chain_in.
Print Assumptions tg_pchain_in.
