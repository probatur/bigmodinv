(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   Each copy constraint is necessary: the full model refines the intended public interface, and the
   model with any one of the four copy constraints removed does not (mutant_wcopy_1_not_refines and its
   three siblings). bmi_all_wires_closed_gen collects these facts, with the presence of all four wires.

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List Lia. Import ListNotations. Open Scope Z_scope.
Require Import Generated.bmi_model_gen.
Require Import Generated.bmi_wires_gen.
Require Import Generated.bmi_scaffold_gen.

Fixpoint expr_eqb (x y:Expr) : bool :=
  match x, y with
  | EConst a, EConst b       => Z.eqb a b
  | ECell a, ECell b         => cell_eqb a b
  | EAdd a1 a2, EAdd b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | ESub a1 a2, ESub b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | EMul a1 a2, EMul b1 b2   => andb (expr_eqb a1 b1) (expr_eqb a2 b2)
  | ENeg a, ENeg b           => expr_eqb a b
  | EScaled a z1, EScaled b z2 => andb (expr_eqb a b) (Z.eqb z1 z2)
  | _, _                     => false
  end.

Definition cut_edge_bmi (e:Cell*Cell) : list (Cell*Cell) :=
  filter (fun f => negb (cellpair_eqb f e)) deployed_copy.
Definition cut_copy_model_bmi (e:Cell*Cell) : CircuitModel :=
  mk_model p deployed_gates (cut_edge_bmi e).

Definition no_gate_reads_bmi (t:Cell) : Prop := forall g, In g deployed_gates -> reads_b t g = false.
Ltac noreads_tac :=
  let g := fresh "g" in let Hin := fresh "Hin" in
  intros g Hin; cbn in Hin;
  repeat (destruct Hin as [<-|Hin]; [vm_compute; reflexivity| ]);
  contradiction.

Definition wit_honest_bmi : Assignment := fun c =>
  if cell_eqb c (0%nat, 0%nat) then 5 else
  if cell_eqb c (1%nat, 0%nat) then 2 else
  if cell_eqb c (4%nat, 0%nat) then 7 else
  if cell_eqb c (7%nat, 0%nat) then 1 else
  if cell_eqb c (8%nat, 0%nat) then 4277505872164533714 else
  if cell_eqb c (9%nat, 0%nat) then 9357044095359917486 else
  if cell_eqb c (10%nat, 0%nat) then 14703926435565584621 else
  if cell_eqb c (12%nat, 0%nat) then 10961108797421617631 else
  if cell_eqb c (13%nat, 0%nat) then 1 else
  if cell_eqb c (20%nat, 0%nat) then 28948022309329048855892746252171976963363056481941560715954676764349967630334 else
  if cell_eqb c (21%nat, 0%nat) then 3 else
  if cell_eqb c (22%nat, 0%nat) then 5 else
  if cell_eqb c (23%nat, 0%nat) then 1 else
  if cell_eqb c (30%nat, 0%nat) then 5 else
  if cell_eqb c (33%nat, 0%nat) then 1 else
  if cell_eqb c (35%nat, 0%nat) then 1 else
  if cell_eqb c (38%nat, 0%nat) then 1 else
  if cell_eqb c (40%nat, 0%nat) then 1 else
  if cell_eqb c (41%nat, 0%nat) then 1 else
  if cell_eqb c (42%nat, 0%nat) then 1 else
  if cell_eqb c (44%nat, 0%nat) then 1 else
  if cell_eqb c (46%nat, 0%nat) then 1 else
  if cell_eqb c (47%nat, 0%nat) then 1 else
  if cell_eqb c (49%nat, 0%nat) then 1 else
  if cell_eqb c (50%nat, 0%nat) then 1 else
  if cell_eqb c (51%nat, 0%nat) then 1 else
  if cell_eqb c (58%nat, 0%nat) then 1 else
  if cell_eqb c (59%nat, 0%nat) then 1 else
  if cell_eqb c (62%nat, 0%nat) then 1 else
  if cell_eqb c (63%nat, 0%nat) then 1 else
  if cell_eqb c (64%nat, 0%nat) then 1 else
  if cell_eqb c (66%nat, 0%nat) then 1 else
  if cell_eqb c (68%nat, 0%nat) then 1 else
  if cell_eqb c (69%nat, 0%nat) then 1 else
  if cell_eqb c (71%nat, 0%nat) then 1 else
  if cell_eqb c (72%nat, 0%nat) then 1 else
  if cell_eqb c (73%nat, 0%nat) then 1 else
  if cell_eqb c (80%nat, 0%nat) then 1 else
  if cell_eqb c (81%nat, 0%nat) then 1 else
  if cell_eqb c (84%nat, 0%nat) then 1 else
  if cell_eqb c (85%nat, 0%nat) then 1 else
  if cell_eqb c (86%nat, 0%nat) then 1 else
  if cell_eqb c (88%nat, 0%nat) then 1 else
  if cell_eqb c (90%nat, 0%nat) then 1 else
  if cell_eqb c (91%nat, 0%nat) then 1 else
  if cell_eqb c (93%nat, 0%nat) then 1 else
  if cell_eqb c (94%nat, 0%nat) then 1 else
  if cell_eqb c (95%nat, 0%nat) then 1 else
  if cell_eqb c (99%nat, 0%nat) then 1 else
  if cell_eqb c (100%nat, 0%nat) then 1 else
  if cell_eqb c (101%nat, 0%nat) then 1 else
  if cell_eqb c (103%nat, 0%nat) then 1 else
  if cell_eqb c (105%nat, 0%nat) then 1 else
  if cell_eqb c (106%nat, 0%nat) then 1 else
  if cell_eqb c (108%nat, 0%nat) then 1 else
  if cell_eqb c (109%nat, 0%nat) then 1 else
  if cell_eqb c (110%nat, 0%nat) then 1 else
  if cell_eqb c (117%nat, 0%nat) then 1 else
  if cell_eqb c (118%nat, 0%nat) then 1 else
  if cell_eqb c (121%nat, 0%nat) then 1 else
  if cell_eqb c (122%nat, 0%nat) then 1 else
  if cell_eqb c (123%nat, 0%nat) then 1 else
  if cell_eqb c (125%nat, 0%nat) then 1 else
  if cell_eqb c (127%nat, 0%nat) then 1 else
  if cell_eqb c (128%nat, 0%nat) then 1 else
  if cell_eqb c (130%nat, 0%nat) then 1 else
  if cell_eqb c (131%nat, 0%nat) then 1 else
  if cell_eqb c (132%nat, 0%nat) then 1 else
  if cell_eqb c (139%nat, 0%nat) then 1 else
  if cell_eqb c (140%nat, 0%nat) then 1 else
  if cell_eqb c (143%nat, 0%nat) then 1 else
  if cell_eqb c (144%nat, 0%nat) then 1 else
  if cell_eqb c (145%nat, 0%nat) then 1 else
  if cell_eqb c (147%nat, 0%nat) then 1 else
  if cell_eqb c (149%nat, 0%nat) then 1 else
  if cell_eqb c (150%nat, 0%nat) then 1 else
  if cell_eqb c (152%nat, 0%nat) then 1 else
  if cell_eqb c (153%nat, 0%nat) then 1 else
  if cell_eqb c (154%nat, 0%nat) then 1 else
  if cell_eqb c (161%nat, 0%nat) then 1 else
  if cell_eqb c (162%nat, 0%nat) then 1 else
  if cell_eqb c (164%nat, 0%nat) then 1 else
  if cell_eqb c (165%nat, 0%nat) then 1 else
  if cell_eqb c (167%nat, 0%nat) then 1 else
  if cell_eqb c (168%nat, 0%nat) then 1 else
  if cell_eqb c (169%nat, 0%nat) then 1 else
  if cell_eqb c (176%nat, 0%nat) then 1 else
  if cell_eqb c (177%nat, 0%nat) then 1 else
  if cell_eqb c (180%nat, 0%nat) then 1 else
  if cell_eqb c (181%nat, 0%nat) then 1 else
  if cell_eqb c (182%nat, 0%nat) then 1 else
  if cell_eqb c (184%nat, 0%nat) then 1 else
  if cell_eqb c (186%nat, 0%nat) then 1 else
  if cell_eqb c (187%nat, 0%nat) then 1 else
  if cell_eqb c (189%nat, 0%nat) then 1 else
  if cell_eqb c (190%nat, 0%nat) then 1 else
  if cell_eqb c (191%nat, 0%nat) then 1 else
  if cell_eqb c (198%nat, 0%nat) then 1 else
  if cell_eqb c (199%nat, 0%nat) then 1 else
  if cell_eqb c (202%nat, 0%nat) then 1 else
  if cell_eqb c (203%nat, 0%nat) then 1 else
  if cell_eqb c (204%nat, 0%nat) then 1 else
  if cell_eqb c (206%nat, 0%nat) then 1 else
  if cell_eqb c (208%nat, 0%nat) then 1 else
  if cell_eqb c (209%nat, 0%nat) then 1 else
  if cell_eqb c (211%nat, 0%nat) then 1 else
  if cell_eqb c (212%nat, 0%nat) then 1 else
  if cell_eqb c (213%nat, 0%nat) then 1 else
  if cell_eqb c (220%nat, 0%nat) then 1 else
  if cell_eqb c (221%nat, 0%nat) then 1 else
  if cell_eqb c (224%nat, 0%nat) then 1 else
  if cell_eqb c (225%nat, 0%nat) then 1 else
  if cell_eqb c (290%nat, 0%nat) then 1 else
  if cell_eqb c (291%nat, 0%nat) then 1 else
  if cell_eqb c (292%nat, 0%nat) then 1 else
  if cell_eqb c (293%nat, 0%nat) then 1 else
  if cell_eqb c (294%nat, 0%nat) then 1 else
  if cell_eqb c (296%nat, 0%nat) then 1 else
  if cell_eqb c (297%nat, 0%nat) then 1 else
  if cell_eqb c (298%nat, 0%nat) then 1 else
  if cell_eqb c (305%nat, 0%nat) then 1 else
  if cell_eqb c (306%nat, 0%nat) then 1 else
  if cell_eqb c (309%nat, 0%nat) then 1 else
  if cell_eqb c (310%nat, 0%nat) then 1 else
  if cell_eqb c (311%nat, 0%nat) then 1 else
  if cell_eqb c (313%nat, 0%nat) then 1 else
  if cell_eqb c (315%nat, 0%nat) then 1 else
  if cell_eqb c (316%nat, 0%nat) then 1 else
  if cell_eqb c (318%nat, 0%nat) then 1 else
  if cell_eqb c (319%nat, 0%nat) then 1 else
  if cell_eqb c (320%nat, 0%nat) then 1 else
  if cell_eqb c (327%nat, 0%nat) then 1 else
  if cell_eqb c (328%nat, 0%nat) then 1 else
  if cell_eqb c (331%nat, 0%nat) then 1 else
  if cell_eqb c (332%nat, 0%nat) then 1 else
  if cell_eqb c (333%nat, 0%nat) then 1 else
  if cell_eqb c (335%nat, 0%nat) then 1 else
  if cell_eqb c (337%nat, 0%nat) then 1 else
  if cell_eqb c (338%nat, 0%nat) then 1 else
  if cell_eqb c (340%nat, 0%nat) then 1 else
  if cell_eqb c (341%nat, 0%nat) then 1 else
  if cell_eqb c (342%nat, 0%nat) then 1 else
  if cell_eqb c (349%nat, 0%nat) then 1 else
  if cell_eqb c (350%nat, 0%nat) then 1 else
  if cell_eqb c (353%nat, 0%nat) then 1 else
  if cell_eqb c (354%nat, 0%nat) then 1 else
  if cell_eqb c (802%nat, 0%nat) then 1 else
  if cell_eqb c (804%nat, 0%nat) then 1 else
  if cell_eqb c (805%nat, 0%nat) then 1 else
  if cell_eqb c (806%nat, 0%nat) then 1 else
  if cell_eqb c (807%nat, 0%nat) then 1 else
  if cell_eqb c (808%nat, 0%nat) then 1 else
  if cell_eqb c (809%nat, 0%nat) then 1 else
  if cell_eqb c (810%nat, 0%nat) then 1 else
  if cell_eqb c (811%nat, 0%nat) then 1 else
  if cell_eqb c (812%nat, 0%nat) then 1 else
  if cell_eqb c (813%nat, 0%nat) then 1 else
  if cell_eqb c (814%nat, 0%nat) then 1 else
  if cell_eqb c (815%nat, 0%nat) then 1 else
  if cell_eqb c (816%nat, 0%nat) then 1 else
  if cell_eqb c (817%nat, 0%nat) then 1 else
  if cell_eqb c (818%nat, 0%nat) then 1 else
  if cell_eqb c (819%nat, 0%nat) then 1 else
  if cell_eqb c (820%nat, 0%nat) then 1 else
  if cell_eqb c (821%nat, 0%nat) then 1 else
  if cell_eqb c (822%nat, 0%nat) then 1 else
  if cell_eqb c (823%nat, 0%nat) then 1 else
  if cell_eqb c (824%nat, 0%nat) then 1 else
  if cell_eqb c (825%nat, 0%nat) then 1 else
  if cell_eqb c (826%nat, 0%nat) then 1 else
  if cell_eqb c (827%nat, 0%nat) then 1 else
  if cell_eqb c (828%nat, 0%nat) then 1 else
  if cell_eqb c (829%nat, 0%nat) then 1 else
  if cell_eqb c (830%nat, 0%nat) then 1 else
  if cell_eqb c (831%nat, 0%nat) then 1 else
  if cell_eqb c (832%nat, 0%nat) then 1 else
  if cell_eqb c (833%nat, 0%nat) then 1 else
  if cell_eqb c (834%nat, 0%nat) then 1 else
  if cell_eqb c (835%nat, 0%nat) then 1 else
  if cell_eqb c (836%nat, 0%nat) then 1 else
  if cell_eqb c (837%nat, 0%nat) then 1 else
  if cell_eqb c (838%nat, 0%nat) then 1 else
  if cell_eqb c (839%nat, 0%nat) then 1 else
  if cell_eqb c (840%nat, 0%nat) then 1 else
  if cell_eqb c (841%nat, 0%nat) then 1 else
  if cell_eqb c (842%nat, 0%nat) then 1 else
  if cell_eqb c (843%nat, 0%nat) then 1 else
  if cell_eqb c (844%nat, 0%nat) then 1 else
  if cell_eqb c (845%nat, 0%nat) then 1 else
  if cell_eqb c (846%nat, 0%nat) then 1 else
  if cell_eqb c (847%nat, 0%nat) then 1 else
  if cell_eqb c (848%nat, 0%nat) then 1 else
  if cell_eqb c (849%nat, 0%nat) then 1 else
  if cell_eqb c (850%nat, 0%nat) then 1 else
  if cell_eqb c (851%nat, 0%nat) then 1 else
  if cell_eqb c (852%nat, 0%nat) then 1 else
  if cell_eqb c (853%nat, 0%nat) then 1 else
  if cell_eqb c (854%nat, 0%nat) then 1 else
  if cell_eqb c (855%nat, 0%nat) then 1 else
  if cell_eqb c (856%nat, 0%nat) then 1 else
  if cell_eqb c (857%nat, 0%nat) then 1 else
  if cell_eqb c (858%nat, 0%nat) then 1 else
  if cell_eqb c (859%nat, 0%nat) then 1 else
  if cell_eqb c (860%nat, 0%nat) then 1 else
  if cell_eqb c (861%nat, 0%nat) then 1 else
  if cell_eqb c (862%nat, 0%nat) then 1 else
  if cell_eqb c (863%nat, 0%nat) then 1 else
  if cell_eqb c (864%nat, 0%nat) then 1 else
  if cell_eqb c (865%nat, 0%nat) then 1 else
  if cell_eqb c (866%nat, 0%nat) then 1 else
  if cell_eqb c (867%nat, 0%nat) then 1 else
  if cell_eqb c (868%nat, 0%nat) then 1 else
  if cell_eqb c (869%nat, 0%nat) then 1 else
  if cell_eqb c (871%nat, 0%nat) then 1 else
  if cell_eqb c (872%nat, 0%nat) then 1 else
  if cell_eqb c (939%nat, 0%nat) then 1 else
  if cell_eqb c (940%nat, 0%nat) then 1 else
  if cell_eqb c (942%nat, 0%nat) then 1 else
  if cell_eqb c (1008%nat, 0%nat) then 1 else
  if cell_eqb c (1009%nat, 0%nat) then 1 else
  if cell_eqb c (1077%nat, 0%nat) then 1 else
  if cell_eqb c (1146%nat, 0%nat) then 1 else
  if cell_eqb c (1215%nat, 0%nat) then 1 else
  if cell_eqb c (1284%nat, 0%nat) then 1 else
  if cell_eqb c (1353%nat, 0%nat) then 1 else
  if cell_eqb c (1422%nat, 0%nat) then 1 else
  if cell_eqb c (1491%nat, 0%nat) then 1 else
  if cell_eqb c (1492%nat, 0%nat) then 1 else
  if cell_eqb c (1494%nat, 0%nat) then 1 else
  if cell_eqb c (1684%nat, 0%nat) then 1 else
  if cell_eqb c (4000%nat, 0%nat) then 4277505872164533714 else
  if cell_eqb c (4000%nat, 1%nat) then 9357044095359917486 else
  if cell_eqb c (4000%nat, 2%nat) then 14703926435565584621 else
  0.

Lemma honest_full_sat_bmi : sat deployed_model wit_honest_bmi.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.

Definition mutant_wcopy_1_model : CircuitModel := cut_copy_model_bmi ((8%nat, 0%nat), (4000%nat, 0%nat)).
Definition wit_wcopy_1 : Assignment := fun c =>
  if cell_eqb c (4000%nat, 0%nat) then 4277505872164533715 else
  wit_honest_bmi c.
Lemma wcopy_1_split_sat : sat mutant_wcopy_1_model wit_wcopy_1.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_1_not_refines : ~ refinesD_bmi_gen mutant_wcopy_1_model intact_ports_bmi_gen.
Proof.
  unfold refinesD_bmi_gen. intro H. specialize (H wit_wcopy_1 wcopy_1_split_sat).
  unfold RD_bmi_gen in H. cbn [ intact_ports_bmi_gen] in H.
  pose proof (proj1 H) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_2_model : CircuitModel := cut_copy_model_bmi ((9%nat, 0%nat), (4000%nat, 1%nat)).
Definition wit_wcopy_2 : Assignment := fun c =>
  if cell_eqb c (4000%nat, 1%nat) then 9357044095359917487 else
  wit_honest_bmi c.
Lemma wcopy_2_split_sat : sat mutant_wcopy_2_model wit_wcopy_2.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_2_not_refines : ~ refinesD_bmi_gen mutant_wcopy_2_model intact_ports_bmi_gen.
Proof.
  unfold refinesD_bmi_gen. intro H. specialize (H wit_wcopy_2 wcopy_2_split_sat).
  unfold RD_bmi_gen in H. cbn [ intact_ports_bmi_gen] in H.
  pose proof (proj1 (proj2 H)) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_3_model : CircuitModel := cut_copy_model_bmi ((10%nat, 0%nat), (4000%nat, 2%nat)).
Definition wit_wcopy_3 : Assignment := fun c =>
  if cell_eqb c (4000%nat, 2%nat) then 14703926435565584622 else
  wit_honest_bmi c.
Lemma wcopy_3_split_sat : sat mutant_wcopy_3_model wit_wcopy_3.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_3_not_refines : ~ refinesD_bmi_gen mutant_wcopy_3_model intact_ports_bmi_gen.
Proof.
  unfold refinesD_bmi_gen. intro H. specialize (H wit_wcopy_3 wcopy_3_split_sat).
  unfold RD_bmi_gen in H. cbn [ intact_ports_bmi_gen] in H.
  pose proof (proj1 (proj2 (proj2 H))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Definition mutant_wcopy_4_model : CircuitModel := cut_copy_model_bmi ((11%nat, 0%nat), (4000%nat, 3%nat)).
Definition wit_wcopy_4 : Assignment := fun c =>
  if cell_eqb c (4000%nat, 3%nat) then 1 else
  wit_honest_bmi c.
Lemma wcopy_4_split_sat : sat mutant_wcopy_4_model wit_wcopy_4.
Proof. split; [ apply gates_holdb_sound; vm_compute; reflexivity | apply copy_holdsb_sound; vm_compute; reflexivity ]. Qed.
Theorem mutant_wcopy_4_not_refines : ~ refinesD_bmi_gen mutant_wcopy_4_model intact_ports_bmi_gen.
Proof.
  unfold refinesD_bmi_gen. intro H. specialize (H wit_wcopy_4 wcopy_4_split_sat).
  unfold RD_bmi_gen in H. cbn [ intact_ports_bmi_gen] in H.
  pose proof (proj2 (proj2 (proj2 H))) as Hc.
  vm_compute in Hc. discriminate Hc.
Qed.

Theorem bmi_all_wires_closed_gen :
  (In ((8%nat, 0%nat), (4000%nat, 0%nat)) deployed_copy /\
   In ((9%nat, 0%nat), (4000%nat, 1%nat)) deployed_copy /\
   In ((10%nat, 0%nat), (4000%nat, 2%nat)) deployed_copy /\
   In ((11%nat, 0%nat), (4000%nat, 3%nat)) deployed_copy) /\
  (refinesD_bmi_gen deployed_model intact_ports_bmi_gen /\
   sat deployed_model wit_honest_bmi) /\
  (~ refinesD_bmi_gen mutant_wcopy_1_model intact_ports_bmi_gen /\
   ~ refinesD_bmi_gen mutant_wcopy_2_model intact_ports_bmi_gen /\
   ~ refinesD_bmi_gen mutant_wcopy_3_model intact_ports_bmi_gen /\
   ~ refinesD_bmi_gen mutant_wcopy_4_model intact_ports_bmi_gen).
Proof.
  split; [| split].
  - repeat split;
      first [ exact in_copy_1
            | exact in_copy_2
            | exact in_copy_3
            | exact in_copy_4 ].
  - split; [ exact deployed_refines_RD_bmi_gen | exact honest_full_sat_bmi ].
  - exact (conj mutant_wcopy_1_not_refines
      (conj mutant_wcopy_2_not_refines
      (conj mutant_wcopy_3_not_refines
      (mutant_wcopy_4_not_refines)))).
Qed.
