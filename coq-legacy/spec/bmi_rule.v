(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   The rule for BigModInv at four limbs of 64 bits: the input assumption PRE_bmi, the enforced relation
   REL_bmi, and the rule R_bmi (the input assumption implies the enforced relation), with facts about
   them. The rule is ours. It answers to two sentences of the public audit of circom-bigint by the
   0xPARC Community, the Ethereum Foundation and Veridise Inc. (2022), quoted below exactly as the
   report renders them. They are third-party text, not covered by this file's licence.

   V-BIGINT-VUL-002, Background: "BigModInv(n,k) takes two inputs in[k] , p[k] representing big integers
   and produces an output out[k] , which is constrained to (out*in)%p=1 ."

   V-BIGINT-VUL-003, Description: "Several templates assume the inputs to be of size n-bits. However,
   this is not explicitly stated to warn the developers."

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith Lia Bool List Znumtheory.
Import ListNotations.

Open Scope Z_scope.

Definition N_BITS : Z := 64.

Definition K : nat := 4.

Definition B : Z := 2 ^ N_BITS.

Lemma N_BITS_val : N_BITS = 64. Proof. reflexivity. Qed.
Lemma K_val : K = 4%nat. Proof. reflexivity. Qed.

Lemma B_pos : 0 < B.
Proof. unfold B, N_BITS. apply Z.pow_pos_nonneg; lia. Qed.

Lemma B_big : 2 <= B.
Proof. unfold B, N_BITS. change 2 with (2^1) at 1. apply Z.pow_le_mono_r; lia. Qed.

Lemma our_n_is_inside_the_real_admissibility : N_BITS <= 126.
Proof. unfold N_BITS. lia. Qed.

(* The value of a vector of limbs: its little-endian base-2^64 (Horner) reading. *)
Definition VAL (v : list Z) : Z := fold_right (fun x acc => x + B * acc) 0 v.

(* The same value as an indexed sum, each limb times its power of 2^64. The sum runs over the
   list's full length, not over a fixed four terms. *)
Definition VAL_indexed (v : list Z) : Z :=
  fold_right Z.add 0 (map (fun i => nth i v 0 * B ^ (Z.of_nat i)) (seq 0 (length v))).

Lemma VAL_nil : VAL [] = 0. Proof. reflexivity. Qed.
Lemma VAL_cons : forall x t, VAL (x :: t) = x + B * VAL t. Proof. reflexivity. Qed.

Lemma fold_add_scaled_map : forall c (g : nat -> Z) l,
  fold_right Z.add 0 (map (fun i => c * g i) l)
  = c * fold_right Z.add 0 (map g l).
Proof.
  intros c g l. induction l as [|y l IH]; cbn [map fold_right]; [ ring | ].
  rewrite IH. ring.
Qed.

Lemma VAL_indexed_cons : forall x t,
  VAL_indexed (x :: t) = x + B * VAL_indexed t.
Proof.
  intros x t. unfold VAL_indexed. cbn [length seq map fold_right].
  cbn [nth]. rewrite Z.pow_0_r, Z.mul_1_r. f_equal.
  rewrite <- (seq_shift (length t) 0), map_map.
  rewrite (map_ext
             (fun i => nth (S i) (x :: t) 0 * B ^ Z.of_nat (S i))
             (fun i => B * (nth i t 0 * B ^ Z.of_nat i))).
  - apply fold_add_scaled_map.
  - intro i. cbn [nth]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

(* The two readings agree for lists of every length. On the rule's domain, where every vector has
   exactly 4 limbs, both are the four-term sum the template describes. *)
Theorem VAL_eq_VAL_indexed : forall v, VAL v = VAL_indexed v.
Proof.
  induction v as [|x t IH]; [ reflexivity | ].
  rewrite VAL_cons, VAL_indexed_cons, IH. reflexivity.
Qed.

Definition limbs_in_range (v : list Z) : Prop :=
  forall i, (i < K)%nat -> 0 <= nth i v 0 < B.

Lemma VAL_bounds : forall v,
  (forall i, (i < length v)%nat -> 0 <= nth i v 0 < B) ->
  0 <= VAL v < B ^ Z.of_nat (length v).
Proof.
  induction v as [|x t IH]; intro H.
  - cbn [VAL fold_right length]. rewrite Z.pow_0_r. lia.
  - cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    rewrite VAL_cons.
    assert (Hx : 0 <= x < B).
    { specialize (H 0%nat). cbn [nth length] in H. apply H. cbn [length]. lia. }
    assert (Ht : 0 <= VAL t < B ^ Z.of_nat (length t)).
    { apply IH. intros i Hi. specialize (H (S i)). cbn [nth] in H.
      apply H. cbn [length]. lia. }
    assert (HB : 0 < B ^ Z.of_nat (length t))
      by (apply Z.pow_pos_nonneg; [ apply B_pos | lia ]).
    pose proof B_pos as HBp.
    nia.
Qed.

Lemma VAL_lt_pow : forall v,
  length v = K -> limbs_in_range v -> 0 <= VAL v < B ^ (Z.of_nat K).
Proof.
  intros v Hl Hr. rewrite <- Hl. apply VAL_bounds.
  intros i Hi. apply Hr. rewrite <- Hl. exact Hi.
Qed.

(* The input assumption: in and p have exactly 4 limbs, each in range. Assumed, never enforced,
   as the template assumes it (V-BIGINT-VUL-003). *)
Definition PRE_bmi (inp p : list Z) : Prop :=
  length inp = K /\ length p = K /\ limbs_in_range inp /\ limbs_in_range p.

(* The enforced relation. The conjunct 1 < VAL p is placed here, among what the circuit must
   enforce; for inputs that satisfy the input assumption, our circuit enforces it with an explicit
   comparator (comparator_forces_the_modulus). *)
Definition REL_bmi (inp p out : list Z) : Prop :=
  length out = K
  /\ limbs_in_range out
  /\ 1 < VAL p
  /\ (VAL inp * VAL out) mod (VAL p) = 1.

(* The rule: the input assumption implies the enforced relation. *)
Definition R_bmi (inp p out : list Z) : Prop :=
  PRE_bmi inp p -> REL_bmi inp p out.

Theorem shifting_out_by_p_preserves_the_relation :
  forall inp p out out',
    REL_bmi inp p out ->
    length out' = K ->
    limbs_in_range out' ->
    VAL out' = VAL out + VAL p ->
    REL_bmi inp p out'.
Proof.
  intros inp p out out' [Hlo [Hro [Hp Hprod]]] Hlo' Hro' Hval.
  split; [ exact Hlo' | ]. split; [ exact Hro' | ]. split; [ exact Hp | ].
  rewrite Hval.
  replace (VAL inp * (VAL out + VAL p))
     with (VAL inp * VAL out + VAL inp * VAL p) by ring.
  rewrite Z.mod_add by lia.
  exact Hprod.
Qed.

Definition P_ANCHOR   : list Z := [7; 0; 0; 1].
Definition INP_ANCHOR : list Z := [5; 2; 0; 0].
Definition OUT_ANCHOR : list Z :=
  [4277505872164533714; 9357044095359917486; 14703926435565584621; 0].

Definition OUT2_ANCHOR : list Z :=
  [4277505872164533721; 9357044095359917486; 14703926435565584621; 1].

Lemma p_anchor_wf : length P_ANCHOR = K. Proof. reflexivity. Qed.
Lemma inp_anchor_wf : length INP_ANCHOR = K. Proof. reflexivity. Qed.
Lemma out_anchor_wf : length OUT_ANCHOR = K. Proof. reflexivity. Qed.
Lemma out2_anchor_wf : length OUT2_ANCHOR = K. Proof. reflexivity. Qed.

Lemma B_value : B = 18446744073709551616.
Proof. unfold B, N_BITS. vm_compute. reflexivity. Qed.

Ltac range_tac :=
  intros i Hi; unfold K in Hi; rewrite B_value;
  do 4 (destruct i as [|i]; [ cbn [nth]; lia | ]);
  lia.

Lemma p_anchor_range : limbs_in_range P_ANCHOR.
Proof. unfold limbs_in_range, P_ANCHOR. range_tac. Qed.

Lemma inp_anchor_range : limbs_in_range INP_ANCHOR.
Proof. unfold limbs_in_range, INP_ANCHOR. range_tac. Qed.

Lemma out_anchor_range : limbs_in_range OUT_ANCHOR.
Proof. unfold limbs_in_range, OUT_ANCHOR. range_tac. Qed.

Lemma out2_anchor_range : limbs_in_range OUT2_ANCHOR.
Proof. unfold limbs_in_range, OUT2_ANCHOR. range_tac. Qed.

Lemma anchor_pre : PRE_bmi INP_ANCHOR P_ANCHOR.
Proof.
  split; [ apply inp_anchor_wf | ]. split; [ apply p_anchor_wf | ].
  split; [ apply inp_anchor_range | apply p_anchor_range ].
Qed.

Example R_bmi_real_inverse_accepted : REL_bmi INP_ANCHOR P_ANCHOR OUT_ANCHOR.
Proof.
  split; [ apply out_anchor_wf | ]. split; [ apply out_anchor_range | ].
  unfold INP_ANCHOR, P_ANCHOR, OUT_ANCHOR, VAL, B, N_BITS.
  split; vm_compute; reflexivity.
Qed.

Example R_bmi_second_representative_ALSO_accepted :
  REL_bmi INP_ANCHOR P_ANCHOR OUT2_ANCHOR.
Proof.
  split; [ apply out2_anchor_wf | ]. split; [ apply out2_anchor_range | ].
  unfold INP_ANCHOR, P_ANCHOR, OUT2_ANCHOR, VAL, B, N_BITS.
  split; vm_compute; reflexivity.
Qed.

Lemma out2_is_out_plus_p : VAL OUT2_ANCHOR = VAL OUT_ANCHOR + VAL P_ANCHOR.
Proof.
  unfold OUT2_ANCHOR, OUT_ANCHOR, P_ANCHOR, VAL, B, N_BITS. vm_compute. reflexivity.
Qed.

(* An inverse representative, never the inverse: two distinct accepted outputs for the same inputs. *)
Theorem out_is_NOT_unique :
  OUT_ANCHOR <> OUT2_ANCHOR
  /\ REL_bmi INP_ANCHOR P_ANCHOR OUT_ANCHOR
  /\ REL_bmi INP_ANCHOR P_ANCHOR OUT2_ANCHOR.
Proof.
  split; [ | split ].
  -

    intro H.
    assert (H3 : nth 3 OUT_ANCHOR 0 = nth 3 OUT2_ANCHOR 0)
      by (rewrite H; reflexivity).
    unfold OUT_ANCHOR, OUT2_ANCHOR in H3. cbn [nth] in H3. discriminate H3.
  - exact R_bmi_real_inverse_accepted.
  - exact R_bmi_second_representative_ALSO_accepted.
Qed.

Definition P_ZERO : list Z := [0; 0; 0; 0].
Definition ONE_V  : list Z := [1; 0; 0; 0].

Lemma p_zero_has_VAL_zero : VAL P_ZERO = 0.
Proof. unfold P_ZERO, VAL. cbn [fold_right]. ring. Qed.

Example R_bmi_zero_modulus_refused : ~ REL_bmi ONE_V P_ZERO ONE_V.
Proof.
  intros [_ [_ [Hp _]]]. rewrite p_zero_has_VAL_zero in Hp. lia.
Qed.

Example the_product_conjunct_alone_would_have_accepted_p_zero :
  (VAL ONE_V * VAL ONE_V) mod (VAL P_ZERO) = 1.
Proof. unfold ONE_V, P_ZERO, VAL. vm_compute. reflexivity. Qed.

Definition P_EVEN : list Z := [8; 0; 0; 1].
Definition INP_EVEN : list Z := [2; 0; 0; 0].

Lemma p_even_is_even : exists m, VAL P_EVEN = 2 * m.
Proof.
  assert (H : VAL P_EVEN mod 2 = 0).
  { unfold P_EVEN, VAL, B, N_BITS. vm_compute. reflexivity. }
  apply Z.mod_divide in H; [ | lia ].
  destruct H as [m Hm]. exists m. lia.
Qed.

Theorem non_coprime_is_refused : forall out,
  ~ REL_bmi INP_EVEN P_EVEN out.
Proof.
  intros out [_ [_ [Hp Hprod]]].
  destruct p_even_is_even as [m Hm].
  assert (Hinp : VAL INP_EVEN = 2)
    by (unfold INP_EVEN, VAL; cbn [fold_right]; ring).

  pose proof (Z.div_mod (VAL INP_EVEN * VAL out) (VAL P_EVEN) ltac:(lia)) as Hdm.
  rewrite Hprod, Hinp, Hm in Hdm.
  lia.
Qed.

Example R_bmi_fraud_product_is_two :
  ~ REL_bmi INP_ANCHOR P_ANCHOR [8555011744329067421; 267344117010283356;
                                 10961108797421617627; 0].
Proof.
  intros [_ [_ [_ Hprod]]].
  unfold INP_ANCHOR, P_ANCHOR, VAL, B, N_BITS in Hprod.
  vm_compute in Hprod. discriminate Hprod.
Qed.

Example R_bmi_fraud_zero_out : ~ REL_bmi INP_ANCHOR P_ANCHOR [0;0;0;0].
Proof.
  intros [_ [_ [_ Hprod]]].
  unfold INP_ANCHOR, P_ANCHOR, VAL, B, N_BITS in Hprod.
  vm_compute in Hprod. discriminate Hprod.
Qed.

Theorem out_limb_out_of_range_is_refused : forall inp p out i,
  (i < K)%nat -> ~ (0 <= nth i out 0 < B) -> ~ REL_bmi inp p out.
Proof. intros inp p out i Hi Hbad [_ [Hr _]]. exact (Hbad (Hr i Hi)). Qed.

Theorem wrong_length_out_is_refused : forall inp p out,
  length out <> K -> ~ REL_bmi inp p out.
Proof. intros inp p out Hbad [Hl _]. exact (Hbad Hl). Qed.

Theorem accepted_rows_have_a_real_modulus : forall inp p out,
  REL_bmi inp p out -> 2 <= VAL p.
Proof. intros inp p out [_ [_ [Hp _]]]. lia. Qed.

(* A product leaving remainder 1 certifies coprimality. *)
Theorem accepted_rows_are_coprime : forall inp p out,
  REL_bmi inp p out -> Z.gcd (VAL inp) (VAL p) = 1.
Proof.
  intros inp p out [_ [_ [Hp Hprod]]].
  assert (Hpz : VAL p <> 0) by lia.
  pose proof (Z.div_mod (VAL inp * VAL out) (VAL p) Hpz) as Hdm.
  rewrite Hprod in Hdm.

  set (q := (VAL inp * VAL out) / VAL p) in *.

  assert (Hb : VAL out * VAL inp + (- q) * VAL p = 1).
  { rewrite (Z.mul_comm (VAL out) (VAL inp)), Hdm. ring. }
  apply Z.bezout_1_gcd. unfold Z.Bezout. exists (VAL out), (- q). exact Hb.
Qed.

Theorem the_relation_bounds_no_input : forall inp p out inp',
  VAL inp' = VAL inp -> REL_bmi inp p out -> REL_bmi inp' p out.
Proof.
  intros inp p out inp' Hv [Hl [Hr [Hp Hprod]]].
  split; [ exact Hl | ]. split; [ exact Hr | ]. split; [ exact Hp | ].
  rewrite Hv. exact Hprod.
Qed.

(* The family form for general limb width and count, argued separately in this section. Nothing
   outside it generalises beyond four limbs of 64 bits. *)
Definition VAL_b (b : Z) (v : list Z) : Z := fold_right (fun x acc => x + b * acc) 0 v.

Definition limbs_in_range_nk (b : Z) (k : nat) (v : list Z) : Prop :=
  forall i, (i < k)%nat -> 0 <= nth i v 0 < b.

Definition PRE_bmi_nk (b : Z) (k : nat) (inp p : list Z) : Prop :=
  length inp = k /\ length p = k
  /\ limbs_in_range_nk b k inp /\ limbs_in_range_nk b k p.

Definition REL_bmi_nk (b : Z) (k : nat) (inp p out : list Z) : Prop :=
  length out = k /\ limbs_in_range_nk b k out
  /\ 1 < VAL_b b p
  /\ (VAL_b b inp * VAL_b b out) mod (VAL_b b p) = 1.

Theorem deployed_is_the_family_at_B_K : forall inp p out,
  REL_bmi inp p out <-> REL_bmi_nk B K inp p out.
Proof.
  intros inp p out.
  unfold REL_bmi, REL_bmi_nk, limbs_in_range, limbs_in_range_nk, VAL, VAL_b.
  tauto.
Qed.

Theorem deployed_pre_is_the_family_pre : forall inp p,
  PRE_bmi inp p <-> PRE_bmi_nk B K inp p.
Proof.
  intros inp p.
  unfold PRE_bmi, PRE_bmi_nk, limbs_in_range, limbs_in_range_nk.
  tauto.
Qed.

Theorem family_is_inhabited_at_a_second_member :
  REL_bmi_nk 256 2 [3; 0] [0; 1] [171; 0].
Proof.
  split; [ reflexivity | ].
  split.
  - intros i Hi. do 2 (destruct i as [|i]; [ cbn [nth]; lia | ]). lia.
  - cbn [VAL_b fold_right]. split; [ lia | vm_compute; reflexivity ].
Qed.

Theorem family_out_is_not_unique : forall b k inp p out out',
  REL_bmi_nk b k inp p out ->
  length out' = k -> limbs_in_range_nk b k out' ->
  VAL_b b out' = VAL_b b out + VAL_b b p ->
  REL_bmi_nk b k inp p out'.
Proof.
  intros b k inp p out out' [Hlo [Hro [Hp Hprod]]] Hlo' Hro' Hval.
  split; [ exact Hlo' | ]. split; [ exact Hro' | ]. split; [ exact Hp | ].
  rewrite Hval.
  replace (VAL_b b inp * (VAL_b b out + VAL_b b p))
     with (VAL_b b inp * VAL_b b out + VAL_b b inp * VAL_b b p) by ring.
  rewrite Z.mod_add by lia. exact Hprod.
Qed.

Print Assumptions N_BITS_val.
Print Assumptions K_val.
Print Assumptions B_pos.
Print Assumptions B_big.
Print Assumptions B_value.
Print Assumptions our_n_is_inside_the_real_admissibility.
Print Assumptions VAL_nil.
Print Assumptions VAL_cons.
Print Assumptions fold_add_scaled_map.
Print Assumptions VAL_indexed_cons.
Print Assumptions VAL_eq_VAL_indexed.
Print Assumptions VAL_bounds.
Print Assumptions VAL_lt_pow.
Print Assumptions shifting_out_by_p_preserves_the_relation.
Print Assumptions p_anchor_wf.
Print Assumptions inp_anchor_wf.
Print Assumptions out_anchor_wf.
Print Assumptions out2_anchor_wf.
Print Assumptions p_anchor_range.
Print Assumptions inp_anchor_range.
Print Assumptions out_anchor_range.
Print Assumptions out2_anchor_range.
Print Assumptions anchor_pre.
Print Assumptions R_bmi_real_inverse_accepted.
Print Assumptions R_bmi_second_representative_ALSO_accepted.
Print Assumptions out2_is_out_plus_p.
Print Assumptions out_is_NOT_unique.
Print Assumptions p_zero_has_VAL_zero.
Print Assumptions R_bmi_zero_modulus_refused.
Print Assumptions the_product_conjunct_alone_would_have_accepted_p_zero.
Print Assumptions p_even_is_even.
Print Assumptions non_coprime_is_refused.
Print Assumptions R_bmi_fraud_product_is_two.
Print Assumptions R_bmi_fraud_zero_out.
Print Assumptions out_limb_out_of_range_is_refused.
Print Assumptions wrong_length_out_is_refused.
Print Assumptions accepted_rows_have_a_real_modulus.
Print Assumptions accepted_rows_are_coprime.
Print Assumptions the_relation_bounds_no_input.
Print Assumptions deployed_is_the_family_at_B_K.
Print Assumptions deployed_pre_is_the_family_pre.
Print Assumptions family_is_inhabited_at_a_second_member.
Print Assumptions family_out_is_not_unique.
