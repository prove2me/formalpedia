-- Prove2me | solution 1 for Logic.CarryChain.carry_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:45:21.80983+00:00
-- url     : https://prove2.me/submissions/23b9bc12-924b-440a-8dec-f83af656c2c2

-- Sol generated from Logic/DenseFinalStepCarryChain.lean
import Mathlib
import Definitions.Def_Logic_DenseFinalStepCarryChain
/-
# NET-25 / Catalog·Logic — Carry-chain automata: the transition is length-general

Formal counterpart of the *transition half* of the NET-25 law
**DENSE-FINAL-STEP-IS-THE-CURE**.

The empirical round (round-net-25, mechanism dissection of the NET-24
stateful-carry-cell cure) measured that in every arm — including the arms whose
full-sequence accuracy at `n = 8` collapsed to `0.002–0.08` — the *final-carry*
probe stayed at `0.86–0.99`.  In other words the recurrent **carry transition**
never lost length-generality; only the **digit readout** at the boundary step
did.

This file makes the transition half a theorem, in the exact sense that is needed
for the mechanism argument:

* `Logic.CarryChain.carry` / `digitOut` — the LSB-first base-`b` addition
  automaton with a one-bit state (`carry_le_one`);
* `Logic.CarryChain.val_digitOut_add_carry` — the *exact* length-general
  invariant: for **every** unroll depth `n`,
  `val d n + c n * b ^ n = val a n + val b n`;
* `Logic.CarryChain.modelStep_eq_*` — a *local-to-global* transfer theorem: any
  learned step function that is pointwise correct on the finitely many reachable
  triples `(x, y, c)` with `x, y < base`, `c ≤ 1` — i.e. exactly the triples a
  training set of depth `≥ 2` already exercises — is automatically correct at
  **every** depth;
* `Logic.CarryChain.exists_lengthGeneral_step` and
  `Logic.CarryChain.no_expressivity_wall` — consequently the observed length
  wall is *not* an expressivity obstruction of the recurrent cell: a correct
  finite step table exists and generalises to all lengths.

The complementary *boundary* half (why a 20-dimensional EOS input and a
384-dimensional one, with byte-identical cell weights, nevertheless train to
different solutions) is in `Logic.DenseFinalStepBoundaryConditioning`.
-/


open Logic.CarryChain

open Finset

/-! ## The carry automaton -/







/-! ## The exact, depth-uniform invariant -/



/-! ## Local-to-global transfer for a *learned* step function -/










/-! ## Lab notes (round-net-25, measured)

Teacher-forced evaluation, plain `n = 5` LSB-first base-10 `a + b = c`,
`bs = 256`, 12000 AdamW steps, 2048 fresh draws per evaluation length.

| arm              | params  | n=8 full        | final-carry probe |
|------------------|---------|-----------------|-------------------|
| cap384-raw s0/s1 | 471,582 | 0.0078 / 0.0063 | 0.86–0.99         |
| proj384  s0/s1   | 335,242 | 1.0000 / 1.0000 | 0.86–0.99         |
| pos28    s0/s1   | 129,830 | 0.0049 / 0.0049 | 0.86–0.99         |
| pad384   s0..s3  | 335,242 | 1.0000 × 4      | 0.86–0.99         |
| pad384-zeroEOS   | 334,878 | 0.7441 / 0.0259 | 0.86–0.99         |
| raw20-192 s0..s6 | 125,214 | 0.0806 … 0.0020 | 0.86–0.99         |

The theorems above say the *transition* column of this table has an exact
depth-uniform solution and that local correctness suffices for it; the
`n = 8 full` column therefore isolates a readout/boundary effect, which is what
`Logic.DenseFinalStepBoundaryConditioning` analyses.
-/


open Logic.CarryChain in
theorem solution{base : ℕ} (hb : 0 < base) {a b : ℕ → ℕ}
    (ha : ∀ i, a i < base) (hbd : ∀ i, b i < base) (n : ℕ) :
    carry base a b n ≤ 1 := by
  induction n with
  | zero => simp [carry]
  | succ n ih =>
      have h : a n + b n + carry base a b n ≤ 2 * base - 1 := by
        have := ha n
        have := hbd n
        omega
      have h1 : (a n + b n + carry base a b n) / base ≤ (2 * base - 1) / base :=
        Nat.div_le_div_right h
      have h2 : (2 * base - 1) / base < 2 := Nat.div_lt_of_lt_mul (by omega)
      simp only [carry]
      omega
