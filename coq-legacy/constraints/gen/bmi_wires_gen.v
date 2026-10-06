(* SPDX-License-Identifier: Apache-2.0
   SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd

   The four copy wires, from the output cells (8..11, 0) to the public cells (4000, 0..3).

   Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them. *)

From Coq Require Import ZArith List. Import ListNotations. Open Scope Z_scope.
Require Import Generated.bmi_model_gen.

Definition wcopy_1 : Cell * Cell := ((8%nat, 0%nat), (4000%nat, 0%nat)).
Definition wcopy_2 : Cell * Cell := ((9%nat, 0%nat), (4000%nat, 1%nat)).
Definition wcopy_3 : Cell * Cell := ((10%nat, 0%nat), (4000%nat, 2%nat)).
Definition wcopy_4 : Cell * Cell := ((11%nat, 0%nat), (4000%nat, 3%nat)).
Definition copy_wires : list (Cell * Cell) :=
  [ wcopy_1; wcopy_2; wcopy_3; wcopy_4 ].

Definition share_wires : list Cell :=
  [  ].
