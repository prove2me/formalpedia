-- Prove2me | Theorems.Thm_PositionalStratum_scan_cost_eq_baseline_iff
-- name    : PositionalStratum.scan_cost_eq_baseline_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:00:28.666932+00:00
-- url     : https://prove2.me/theorems/5891ea08-61e8-40e3-a6f5-34c3871a2e59
-- title:
--   Equality case.
-- statement:
--   **Equality case.**  For a descending weight, the expected scan cost equals the full-scan
--   baseline exactly when the weight is flat on the positional space.
--
--   ```lean
--   theorem PositionalStratum.scan_cost_eq_baseline_iff{M : ℕ} (hM : 0 < M) {w : ℕ → ℝ}
--       (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
--       (htot : mass (positions M) w = 1) :
--       EC M scanCost w = baselineC0 M ↔ ∀ i ∈ positions M, ∀ j ∈ positions M, w i = w j := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PositionalStratumStrictMajorization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PositionalStratumStrictMajorization.lean#L114

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

theorem PositionalStratum.scan_cost_eq_baseline_iff{M : ℕ} (hM : 0 < M) {w : ℕ → ℝ}
    (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
    (htot : mass (positions M) w = 1) :
    EC M scanCost w = baselineC0 M ↔ ∀ i ∈ positions M, ∀ j ∈ positions M, w i = w j := by sorry
