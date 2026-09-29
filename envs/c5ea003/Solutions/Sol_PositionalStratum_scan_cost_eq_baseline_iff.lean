-- Prove2me | solution 1 for PositionalStratum.scan_cost_eq_baseline_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:31.768095+00:00
-- url     : https://prove2.me/submissions/af73b1e7-df68-4699-a916-6f517d1849bd

-- Sol generated from Applications/PositionalStratumStrictMajorization.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_card_positions
import Theorems.Thm_PositionalStratum_mem_positions
import Theorems.Thm_PositionalStratum_scan_cost_lt_baseline
import Theorems.Thm_PositionalStratum_sum_positions
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
theorem solution{M : ℕ} (hM : 0 < M) {w : ℕ → ℝ}
    (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
    (htot : mass (positions M) w = 1) :
    EC M scanCost w = baselineC0 M ↔ ∀ i ∈ positions M, ∀ j ∈ positions M, w i = w j := by
  classical
  constructor
  · intro heq i hi j hj
    by_contra hne
    -- a strict drop somewhere contradicts equality via strict majorization
    rcases lt_or_gt_of_ne hne with h | h
    · have hij : j < i := by
        by_contra hcon
        push_neg at hcon
        exact absurd (hanti i hi j hj hcon) (by linarith)
      exact absurd heq (ne_of_lt (scan_cost_lt_baseline hanti htot hj hi hij h))
    · have hij : i < j := by
        by_contra hcon
        push_neg at hcon
        exact absurd (hanti j hj i hi hcon) (by linarith)
      exact absurd heq (ne_of_lt (scan_cost_lt_baseline hanti htot hi hj hij h))
  · intro hflat
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hne : (positions M).Nonempty := by
      refine ⟨1, ?_⟩
      rw [mem_positions]
      omega
    obtain ⟨i₀, hi₀⟩ := hne
    have hconst : ∀ i ∈ positions M, w i = w i₀ := fun i hi => hflat i hi i₀ hi₀
    have hsum : ∑ i ∈ positions M, w i = (M : ℝ) * w i₀ := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_positions, nsmul_eq_mul]
    have hval : w i₀ = 1 / (M : ℝ) := by
      have : (M : ℝ) * w i₀ = 1 := by rw [← hsum]; exact htot
      field_simp at this ⊢
      linarith
    have hEC : EC M scanCost w = (∑ i ∈ positions M, scanCost i) * w i₀ := by
      rw [EC, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i hi => by rw [hconst i hi]
    have hsumc : ∑ i ∈ positions M, scanCost i = (M : ℝ) * ((M : ℝ) + 1) / 2 := by
      simpa [scanCost] using sum_positions M
    rw [hEC, hsumc, hval, baselineC0]
    field_simp
