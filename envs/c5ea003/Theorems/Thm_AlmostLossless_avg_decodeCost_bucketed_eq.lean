-- Prove2me | Theorems.Thm_AlmostLossless_avg_decodeCost_bucketed_eq
-- name    : AlmostLossless.avg_decodeCost_bucketed_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:15:36.492207+00:00
-- url     : https://prove2.me/theorems/ebaea055-b05d-4479-8a25-10ed3b1415b2
-- title:
--   Exact expected decoder complexity.
-- statement:
--   **Exact expected decoder complexity.**  For a pairwise independent bucket
--   hash the bucketed decoder tests exactly `1 + (|T|-1)/m₁` candidates on average
--   over the seed — an identity, so the bound of `avg_decodeCost_bucketed_le` is
--   attained.
--
--   ```lean
--   theorem AlmostLossless.avg_decodeCost_bucketed_eq[Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
--       [Fintype M₁] [Nonempty M₁] (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
--       (hpi : PairwiseIndependent h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
--       (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
--           ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
--         = 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Complexity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Complexity.lean#L66

-- Thm stub generated from Logic/AlmostLossless/Complexity.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Hashing
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

omit [DecidableEq M₂] in

theorem AlmostLossless.avg_decodeCost_bucketed_eq[Fintype A₁] [DecidableEq A₁] [Nonempty A₁]
    [Fintype M₁] [Nonempty M₁] (T : Finset S) {h₁ : A₁ → S → M₁} (h₂ : A₂ → S → M₂)
    (hpi : PairwiseIndependent h₁) (a₂ : A₂) {x : S} (hx : x ∈ T) :
    (∑ a₁ : A₁, (((bucketed T h₁ h₂).decodeCost (a₁, a₂)
        ((bucketed T h₁ h₂).hash (a₁, a₂) x) : ℕ) : ℚ)) / (Fintype.card A₁ : ℚ)
      = 1 + ((T.erase x).card : ℚ) / (Fintype.card M₁ : ℚ) := by sorry
