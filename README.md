<!-- SPDX-License-Identifier: Apache-2.0 -->
<!-- SPDX-FileCopyrightText: 2026 Next Ridge Solutions Ltd -->

# BigModInv, verified: sound and complete

A formally verified BigModInv, soundness and completeness, kernel-checked, at four limbs of 64 bits each
(*n* = 64, *k* = 4).

BigModInv is the modular-inverse template of the circom-bigint library. Given two big integers *in* and *p*,
each written as *k* limbs of *n* bits, it constrains an output *out* so that *in* · *out* leaves remainder 1 on
division by *p*. The public audit of that library, *Auditing Report for circom-bigint (circomlib)* (0xPARC
Community, Ethereum Foundation and Veridise Inc., 2022), lists BigModInv as "In Progress" in its table of
templates.

This repository holds **our own circuit** for that job and **our own written rule** for it, and a proof, checked
by the Coq kernel, that the two agree exactly:

- **sound**: every filling of the circuit's cells that the circuit accepts yields an operand triple the rule
  accepts;
- **complete**: every operand triple that satisfies the rule's input assumption and that the rule accepts is
  realised by some filling the circuit accepts.

The two directions are one theorem, `policy_adequacy_bmi`. No code from circom-bigint is in this repository: the
circuit is our own implementation of the same arithmetic, and the rule is stated from the mathematics and from
the audit report's own description of the template.

## Check it yourself

```
git clone https://github.com/probatur/bigmodinv
cd bigmodinv
docker build .
```

The build compiles every proof from source in the public Coq 8.20.1 image, pinned by digest in the Dockerfile,
then re-checks the whole development, together with the parts of Coq's standard library it uses, with coqchk,
Coq's independent kernel checker. It fails unless coqchk accepts everything and reports no axioms, and its last
step prints the theorem exactly as the kernel states it (reproduced below). With BuildKit, add
`--progress=plain` to see every line. The same build runs on every push, from `.github/workflows/check.yml`. If
you run it, you are welcome to add a line to [REPRODUCTIONS.md](REPRODUCTIONS.md).

## The theorem, as the kernel states it

<!-- STATEMENT:BEGIN (filled from the check's own output; never edited by hand) -->

```
policy_adequacy_bmi
     : (forall a : bmi_scaffold_gen.Assignment,
        bmi_scaffold_gen.sat bmi_model_gen.deployed_model a ->
        bmi_semantic.CANON_bmi a ->
        bmi_rule.PRE_bmi (bmi_semantic.inp_l a) (bmi_semantic.p_l a) ->
        bmi_rule.REL_bmi (bmi_semantic.inp_l a) (bmi_semantic.p_l a)
          (bmi_semantic.out_l a)) /\
       (forall inp pl out : list BinNums.Z,
        bmi_rule.PRE_bmi inp pl ->
        bmi_rule.R_bmi inp pl out ->
        BinInt.Z.gcd (bmi_rule.VAL inp) (bmi_rule.VAL pl) =
        BinNums.Zpos BinNums.xH ->
        exists al : bmi_scaffold_gen.Assignment,
          bmi_scaffold_gen.sat bmi_model_gen.deployed_model al /\
          bmi_semantic.CANON_bmi al /\
          bmi_rule.PRE_bmi (bmi_semantic.inp_l al) (bmi_semantic.p_l al) /\
          bmi_semantic.inp_l al = inp /\
          bmi_semantic.p_l al = pl /\ bmi_semantic.out_l al = out)
```

<!-- STATEMENT:END -->

## The theorem in plain language

### The two objects it connects

**The circuit.** A fixed arithmetic circuit over the prime field of the 255-bit Pasta prime
2^254 + 45560315531419706090280762371685220353. It is a table of cells, each holding a field element, together
with 1,758 polynomial constraints, each of which must evaluate to zero in the field, and 4 copy constraints, each
requiring an output cell and a public cell to hold the same value. A filling of the cells that passes all 1,758
polynomial constraints and all 4 copy constraints is an **accepted assignment** (`sat deployed_model` in the
development). That is the whole acceptance condition: the model contains no lookup tables and no other kind of
constraint.

**The rule** (`coq/spec/bmi_rule.v`), written by us, about triples of vectors (*in*, *p*, *out*). A vector has
limbs; a limb is a whole number from 0 up to, but not including, 2^64; a vector's value `VAL` is its
little-endian base-2^64 reading. The rule has two parts, kept separate on purpose:

- **the input assumption** `PRE_bmi`, about *in* and *p*: each has exactly 4 limbs, and every limb is in range.
  This is the template's own input assumption, which the template does not state and the audit report
  records as a finding (V-BIGINT-VUL-003). It is assumed, never enforced, exactly as the template assumes it.
- **the enforced relation** `REL_bmi`, about the whole triple: *out* has exactly 4 limbs, all in range; the value
  of *p* exceeds 1; and `VAL in · VAL out` leaves remainder exactly 1 on division by `VAL p`.

The rule proper, `R_bmi`, is the implication: **if** the input assumption holds, **then** the enforced relation
holds.

### Soundness: nothing the circuit accepts escapes the rule

For every accepted assignment, read the twelve operand cells (four for *in*, four for *p*, four for *out*), each
as its canonical remainder modulo the field prime. If the *in* and *p* so read satisfy the input assumption, then
the triple so read satisfies the enforced relation (`bridge_sound`).

- The quantifier really is over **all** fillings. Accepted fillings whose *in* or *p* cells are out of range are
  not excluded; the rule asserts nothing about them, because its input assumption fails. That is the template's
  own posture: input ranges are the caller's burden.
- The public cells are not assumed to agree with the output cells: that agreement is derived from the copy
  constraints (`answer_pins_are_DERIVED`).

### Completeness: nothing the rule accepts, within its input assumption, is beyond the circuit

For every triple satisfying the input assumption and the enforced relation, there is a filling that the circuit
accepts, passing all 1,758 polynomial constraints and all 4 copy constraints, whose twelve operand cells read
back as **exactly that triple**, *out* included, limb for limb (`bridge_complete`).

- The filling reads back to the **given** output, not to a preferred or reduced one.
- The covered triples include the uncomfortable ones: inputs whose value is at least the value of *p*, since
  nothing requires *in* to arrive reduced; and moduli whose value exceeds the field prime itself (see the next
  section).

### Two pairs that are easy to confuse

- **The field prime and the modulus *p*.** The circuit's constraints are equations over a fixed prime field of
  about 2^254 elements. The rule's *p* is a 4-limb value chosen by the problem instance, anywhere from 2 up to
  nearly 2^256. They are unrelated quantities; the theorem's arithmetic bridges them. The constraints hold in the
  field, and the rule's conclusion holds over the ordinary integers.
- **An inverse representative, never the inverse.** Like the template, the rule bounds each output limb and
  nothing else. Adding *p* to an accepted output gives another accepted output whenever the result still fits in
  four limbs (`shifting_out_by_p_preserves_the_relation`), and the rule file exhibits two distinct accepted
  outputs for the same inputs (`out_is_NOT_unique`). The output is not unique, as a proved fact rather than a
  caveat, which is why every sentence here says the output carries an inverse representative with 64-bit limbs,
  never the inverse.

## Where each part of the rule comes from

| part of the rule | what it says | where it comes from |
|---|---|---|
| `PRE_bmi` | *in* and *p* have exactly 4 limbs, each in [0, 2^64) | the template's input assumption, recorded by the audit report as V-BIGINT-VUL-003 (quoted below); carried as an assumption, as the template carries it |
| `REL_bmi`, first two conjuncts | *out* has exactly 4 limbs, each in [0, 2^64) | the template's own output check: it range-checks each output limb with `Num2Bits(n)` (circom-bigint, `circuits/bigint.circom`, lines 505–538, commit `7505e5c60b8bc76cfb5cc06646d81aafbae66180`) |
| `REL_bmi`, third conjunct | `1 < VAL p` | our choice of placement, see the reading notes |
| `REL_bmi`, fourth conjunct | `(VAL in · VAL out) mod VAL p = 1` | the audit report's own statement of the template's constraint, V-BIGINT-VUL-002 (quoted below) |
| completeness premise | `Z.gcd (VAL in) (VAL p) = 1` | ours; provably redundant, see the reading notes |

The two sentences from the audit report, quoted exactly as the report renders them. They are third-party text,
not covered by this repository's licence:

> V-BIGINT-VUL-002 (Background): "BigModInv(n,k) takes two inputs in[k] , p[k] representing big integers and
> produces an output out[k] , which is constrained to (out*in)%p=1 ."

> V-BIGINT-VUL-003 (Description): "Several templates assume the inputs to be of size n-bits. However, this is
> not explicitly stated to warn the developers."

## Reading notes

1. **Counting the constraints.** The circuit has 1,758 polynomial constraints and 4 copy constraints; the
   theorem covers exactly the set of fillings that passes both kinds together. The count of 1,758 polynomial
   constraints, beside the 4 copy constraints, is itself a checked fact of the development (`dg_len`).
2. **Completeness is universal.** It holds for every triple that satisfies the input assumption and that the
   rule accepts. The development also runs the construction at a worked example: a second accepted output for
   the anchor inputs, the anchor answer shifted by *p* (`completeness_admits_the_SECOND_representative`); that
   is an instance shown, not the evidence.
3. **An inverse representative, never the inverse.** See above: the output is not unique
   (`out_is_NOT_unique`), and completeness realises every output the rule accepts for inputs that satisfy
   the input assumption, not a preferred one.
4. **Two premises on the statement do no work, and the development proves it.** The soundness side carries a
   canonicity premise, `CANON_bmi`; it is provably satisfied by every filling (`CANON_is_free`), so it narrows
   nothing. The completeness side carries a coprimality premise; it is provably redundant, because a product
   leaving remainder 1 is itself a certificate of coprimality (`the_gcd_premise_is_a_THEOREM`), and the
   premise-free form is proved beside it (`bridge_complete_sharp`). Both premises are on the statement only for
   its shape; neither is load-bearing.
5. **Why `1 < VAL p` is part of the enforced relation.** The rule places *the value of p exceeds 1* among the
   conclusions the circuit must enforce, rather than among the input assumptions. The product condition alone
   would not exclude a zero modulus: in Coq's integer arithmetic *x* mod 0 = *x*, and the rule file exhibits a
   row with *p* = 0 that satisfies the product condition
   (`the_product_conjunct_alone_would_have_accepted_p_zero`), which the full relation does not accept. The
   placement is grounded in our circuit, which contains an explicit comparator: for every accepted filling whose
   inputs satisfy the input assumption, the development proves that the value of *p* is 2 more than the value of
   four in-range limbs (`comparator_forces_the_modulus`), and so exceeds 1 (`modulus_exceeds_one`).
6. **Two readings of a vector's value.** `VAL` is the Horner reading; `VAL_indexed` is the indexed sum of each
   limb times its power of 2^64. `VAL_eq_VAL_indexed` proves them equal for lists of every length. Note that
   `VAL_indexed` sums over the list's full length, not over a fixed four terms. On the rule's domain, where
   every vector has exactly 4 limbs, that is the four-term sum the template describes.
7. **Scope.** Scope: these results bind the formal (Coq) layer only; the generated constraint model's fidelity to the circuit implementation, and the implementation itself, are outside them.

## What is not claimed

- **Nothing about circom-bigint's own circuit or its proofs.** The circuit proved here is ours, built for the
  same function; the rule is ours. We designed our circuit to meet our rule.
- **Nothing beyond the parameter set *n* = 64, *k* = 4**, except where the rule file argues a family form
  separately, in its own section.
- **Nothing about the layers below the formal model.** That the generated constraint model (the 1,758 polynomial
  constraints, the 4 copy constraints, the field prime, the cell layout, and the absence of lookups and of other
  constraint kinds) faithfully mirrors the circuit implementation is outside this claim, as are the
  implementation, the prover and the verifier themselves.
- **No uniqueness of the output, and no bound on the input's value** relative to *p*: the rule deliberately says
  nothing about either, matching the template.

## A proof about a circuit, not a proof made by one

Two different objects are called "proofs" around circuits like this one. This repository contains the first: a
single machine-checked argument, in Coq, about what the circuit's constraints accept. It is checked once, and it
holds for every execution. The circuit itself, when used, produces a different kind of proof, a
zero-knowledge proof for each execution. None of those is in this repository, and nothing here depends on them.

## Files

| file | what it holds |
|---|---|
| `coq/spec/bmi_rule.v` | the rule: `PRE_bmi`, `REL_bmi`, `R_bmi`, and facts about it |
| `coq/constraints/gen/bmi_model_gen.v` | the circuit's constraint model: the field prime, the 1,758 polynomial constraints, the 4 copy constraints |
| `coq/constraints/gen/bmi_scaffold_gen.v` | cells, assignments, evaluation, and the acceptance predicate `sat` |
| `coq/constraints/gen/bmi_wires_gen.v` | the four copy wires, from the output cells to the public cells |
| `coq/constraints/gen/bmi_necessity_gen.v` | each copy constraint is necessary: the full model refines the intended public interface, and with any one of the four removed the model does not (`mutant_wcopy_1_not_refines` and its three siblings) |
| `coq/constraints/pfcs.v` | a Coq embedding of prime-field constraint systems, following the PFCS formalism |
| `coq/constraints/range_field.v`, `coq/constraints/range_field_pasta.v` | field arithmetic, and a primality certificate for the Pasta prime |
| `coq/constraints/field_order_lift.v`, `coq/constraints/bits_kit.v` | lifting facts from the field to the integers; bit decompositions |
| `coq/constraints/bmi_semantic.v` | reading operand triples off a filling |
| `coq/constraints/bmi_soundness.v` | soundness (`bridge_sound`) |
| `coq/constraints/bmi_adequacy.v` | completeness, and the two directions as one theorem (`policy_adequacy_bmi`) |

## Credits

- The PFCS formalism: A. Coglio, E. McCarthy, E. W. Smith, *Formal Verification of Zero-Knowledge Circuits*,
  arXiv:2311.08858 (ACL2 Workshop 2023). `coq/constraints/pfcs.v` follows it.
- circom-bigint, by its authors (GPL-3.0), whose BigModInv template this work answers to. Its behaviour is
  described here; none of its code is copied.
- *Auditing Report for circom-bigint (circomlib)*, 0xPARC Community, Ethereum Foundation and Veridise Inc., 2022.

## Licence

Apache-2.0: see [LICENSE](LICENSE) and [NOTICE](NOTICE). The two quoted sentences from the audit report are
third-party text and are not covered by that licence.

## Contact

Probatur is published by Next Ridge Solutions Ltd: [nxridge.com](https://nxridge.com).
