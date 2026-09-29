-- Prove2me | solution 1 for PositionalStratum.chebyshev_double_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:59:12.373797+00:00
-- url     : https://prove2.me/submissions/77a5bad5-8eea-4942-9d81-ccfa6f4407a7

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
theorem solution(S : Finset ℕ) (c w : ℕ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S, (c i - c j) * (w i - w j)
      = 2 * ((S.card : ℝ) * (∑ i ∈ S, c i * w i) - (∑ i ∈ S, c i) * ∑ i ∈ S, w i) := by
  have h : ∀ i ∈ S, ∑ j ∈ S, (c i - c j) * (w i - w j)
      = (S.card : ℝ) * (c i * w i) - c i * (∑ j ∈ S, w j) - w i * (∑ j ∈ S, c j)
        + ∑ j ∈ S, c j * w j := by
    intro i _
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl h]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring
