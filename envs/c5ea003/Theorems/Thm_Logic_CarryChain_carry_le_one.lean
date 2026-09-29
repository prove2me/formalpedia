-- Prove2me | Theorems.Thm_Logic_CarryChain_carry_le_one
-- name    : Logic.CarryChain.carry_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:25:20.04693+00:00
-- url     : https://prove2.me/theorems/6b9547e4-725f-4cf7-a9a7-443952e4f02d
-- title:
--   The carry state is a single bit, as soon as the inputs are genuine digits.
-- statement:
--   The carry state is a single bit, as soon as the inputs are genuine digits.
--
--   ```lean
--   theorem Logic.CarryChain.carry_le_one{base : ℕ} (hb : 0 < base) {a b : ℕ → ℕ}
--       (ha : ∀ i, a i < base) (hbd : ∀ i, b i < base) (n : ℕ) :
--       carry base a b n ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DenseFinalStepCarryChain.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DenseFinalStepCarryChain.lean#L65

-- Thm stub generated from Logic/DenseFinalStepCarryChain.lean
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

theorem Logic.CarryChain.carry_le_one{base : ℕ} (hb : 0 < base) {a b : ℕ → ℕ}
    (ha : ∀ i, a i < base) (hbd : ∀ i, b i < base) (n : ℕ) :
    carry base a b n ≤ 1 := by sorry
