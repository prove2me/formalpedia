-- Prove2me | solution 1 for PositionalStratum.pairwise_term_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:59:27.367596+00:00
-- url     : https://prove2.me/submissions/e89525a6-4c10-45db-a661-5a56ea413b8c

-- Sol generated from Applications/PositionalStratumStrictMajorization.lean
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







open PositionalStratum in
theorem solution{M : ℕ} {w : ℕ → ℝ}
    (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
    {i j : ℕ} (hi : i ∈ positions M) (hj : j ∈ positions M) :
    (scanCost i - scanCost j) * (w i - w j) ≤ 0 := by
  simp only [scanCost]
  rcases le_total i j with h | h
  · have hw : w j ≤ w i := hanti i hi j hj h
    have hc : (i : ℝ) - j ≤ 0 := by
      have : (i : ℝ) ≤ j := by exact_mod_cast h
      linarith
    exact mul_nonpos_of_nonpos_of_nonneg hc (by linarith)
  · have hw : w i ≤ w j := hanti j hj i hi h
    have hc : (0 : ℝ) ≤ (i : ℝ) - j := by
      have : (j : ℝ) ≤ i := by exact_mod_cast h
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hc (by linarith)
