-- Prove2me | Theorems.Thm_AlmostLossless_card_typical_sq_le_card_mul_sum_decodeCost
-- name    : AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:07.346118+00:00
-- url     : https://prove2.me/theorems/5eeb8859-b462-4a89-9391-6a1cbdad7def
-- title:
--   Universal lower bound on decoding work (Cauchy–Schwarz over buckets).
-- statement:
--   **Universal lower bound on decoding work (Cauchy–Schwarz over buckets).**
--   For any scan scheme and any seed, the total number of candidate tests spent
--   decoding the whole typical set is at least `|T|²/|M|`.  Averaged over a typical
--   word this says: `m` codewords force `t/m` expected tests, whatever the scheme.
--
--   ```lean
--   theorem AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost(P : ScanScheme S A M) (a : A) :
--       (P.typical.card : ℚ) ^ 2
--         ≤ (Fintype.card M : ℚ) * ∑ x ∈ P.typical, (P.decodeCost a (P.hash a x) : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Complexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Complexity.lean#L111

-- Thm stub generated from Logic/AlmostLossless/Complexity.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme

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



variable {A₁ A₂ M₁ M₂ : Type*} [DecidableEq M₁] [DecidableEq M₂]



/-! ## A universal lower bound on decoder work -/

variable [Fintype M]



omit [DecidableEq S] in

theorem AlmostLossless.card_typical_sq_le_card_mul_sum_decodeCost(P : ScanScheme S A M) (a : A) :
    (P.typical.card : ℚ) ^ 2
      ≤ (Fintype.card M : ℚ) * ∑ x ∈ P.typical, (P.decodeCost a (P.hash a x) : ℚ) := by sorry
