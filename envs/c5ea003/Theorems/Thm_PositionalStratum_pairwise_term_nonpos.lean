-- Prove2me | Theorems.Thm_PositionalStratum_pairwise_term_nonpos
-- name    : PositionalStratum.pairwise_term_nonpos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:00:21.250379+00:00
-- url     : https://prove2.me/theorems/bfe83f94-acf9-46af-9a63-b05d5dc77bd0
-- title:
--   Under antitonicity every pairwise term of the double sum is nonpositive.
-- statement:
--   Under antitonicity every pairwise term of the double sum is nonpositive.
--
--   ```lean
--   theorem PositionalStratum.pairwise_term_nonpos{M : ℕ} {w : ℕ → ℝ}
--       (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
--       {i j : ℕ} (hi : i ∈ positions M) (hj : j ∈ positions M) :
--       (scanCost i - scanCost j) * (w i - w j) ≤ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumStrictMajorization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumStrictMajorization.lean#L46

-- Thm stub generated from Applications/PositionalStratumStrictMajorization.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
/-
# Strict majorization : the descending arrangement strictly beats the baseline

`Applications.PositionalStratumMeasure.scan_cost_le_baseline` gives the majorization step
`C_sort ≤ C₀ = (M+1)/2` of the master chain.  This file sharpens it to the *strict*
statement, which is what makes the master chain informative rather than vacuous:

  a descending weight that is **not flat** — i.e. `w b < w a` for some earlier slot `a` —
  has expected scan cost *strictly* below the full-scan baseline (`scan_cost_lt_baseline`),

together with the corresponding equality characterisation (`scan_cost_eq_baseline_iff`):
equality holds exactly on the flat (uniform) weight.

The engine is the exact **Chebyshev double-sum identity** (`chebyshev_double_sum`)

  `∑_i ∑_j (c i - c j)(w i - w j) = 2 (|S| ∑_i c i w i - (∑ c)(∑ w))`,

whose termwise sign analysis under antitonicity yields both the inequality and its
equality case.  This is a genuine second-order refinement: the inequality version follows
from Mathlib's Chebyshev lemma, the strict version does not.
-/

open PositionalStratum

open Finset

noncomputable section

theorem PositionalStratum.pairwise_term_nonpos{M : ℕ} {w : ℕ → ℝ}
    (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
    {i j : ℕ} (hi : i ∈ positions M) (hj : j ∈ positions M) :
    (scanCost i - scanCost j) * (w i - w j) ≤ 0 := by sorry
