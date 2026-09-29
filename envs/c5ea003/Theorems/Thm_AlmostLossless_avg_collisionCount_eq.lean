-- Prove2me | Theorems.Thm_AlmostLossless_avg_collisionCount_eq
-- name    : AlmostLossless.avg_collisionCount_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:21.469877+00:00
-- url     : https://prove2.me/theorems/24754aa6-bc90-4f09-9470-2af570e4e428
-- title:
--   Avg collisionCount eq
-- statement:
--   Formal statement of `AlmostLossless.avg_collisionCount_eq` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AlmostLossless.avg_collisionCount_eq[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [Nonempty M]
--       {h : A → S → M} (hpi : PairwiseIndependent h) (T : Finset S) (x : S) :
--       (∑ a : A, (collisionCount h T a x : ℚ)) / (Fintype.card A : ℚ)
--         = ((T.erase x).card : ℚ) / (Fintype.card M : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Complexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Complexity.lean#L34

-- Thm stub generated from Logic/AlmostLossless/Complexity.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
import Definitions.Def_Logic_AlmostLossless_Instances

/-!
# Decoder complexity: an exact expected cost and a universal lower bound

The rate side of almost-lossless compression is settled by `Core`; this file is
about the *time* side, which the research thread identifies as the real
obstacle.

* `AlmostLossless.avg_decodeCost_bucketed_eq` — for a **pairwise independent**
  hash family the expected number of candidate tests performed by the bucketed
  decoder on a typical word is *exactly* `1 + (|T|-1)/m₁`, matching the
  numerical measurements (Section 4 of `ComputationalEvidence.md`) to the digit.
  So the upper bound `avg_decodeCost_bucketed_le` cannot be improved for this
  class of families.

* `AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost` — a *universal*
  lower bound: for **every** scan scheme and every seed, the total decoding work
  over the typical set is at least `|T|²/|M|` (Cauchy–Schwarz over the buckets),
  and each individual decoding costs at least one test.  Hence no scheme with
  `m` codewords can decode a typical set of size `t` in less than `t/m` expected
  tests: rate and decoding time obey a hyperbolic trade-off.

Together these pin the bucketed decoder to within an additive `1` of optimal.
-/

open AlmostLossless

open Finset

variable {S A M : Type*} [DecidableEq S] [DecidableEq M]

/-! ## Exact expected work for pairwise independent families -/

theorem AlmostLossless.avg_collisionCount_eq[Fintype A] [DecidableEq A] [Nonempty A] [Fintype M] [Nonempty M]
    {h : A → S → M} (hpi : PairwiseIndependent h) (T : Finset S) (x : S) :
    (∑ a : A, (collisionCount h T a x : ℚ)) / (Fintype.card A : ℚ)
      = ((T.erase x).card : ℚ) / (Fintype.card M : ℚ) := by sorry
