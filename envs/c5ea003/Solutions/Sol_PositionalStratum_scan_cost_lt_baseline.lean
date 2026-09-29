-- Prove2me | solution 1 for PositionalStratum.scan_cost_lt_baseline
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:02:12.919825+00:00
-- url     : https://prove2.me/submissions/82e81a4b-d96f-4117-af07-a20e21c174f8

-- Sol generated from Applications/PositionalStratumStrictMajorization.lean
import Mathlib
import Definitions.Def_Applications_PositionalStratumMeasure
import Theorems.Thm_PositionalStratum_card_positions
import Theorems.Thm_PositionalStratum_chebyshev_double_sum
import Theorems.Thm_PositionalStratum_mem_positions
import Theorems.Thm_PositionalStratum_pairwise_term_nonpos
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
theorem solution{M : ℕ} {w : ℕ → ℝ}
    (hanti : ∀ i ∈ positions M, ∀ j ∈ positions M, i ≤ j → w j ≤ w i)
    (htot : mass (positions M) w = 1)
    {a b : ℕ} (ha : a ∈ positions M) (hb : b ∈ positions M) (hab : a < b) (hdrop : w b < w a) :
    EC M scanCost w < baselineC0 M := by
  classical
  have hMpos : 0 < M := by
    rcases mem_positions.mp ha with ⟨h1, h2⟩
    omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  -- the inner sums are nonpositive, and the one at `a` is strictly negative
  have hinner_nonpos : ∀ i ∈ positions M,
      ∑ j ∈ positions M, (scanCost i - scanCost j) * (w i - w j) ≤ 0 := by
    intro i hi
    exact Finset.sum_nonpos fun j hj => pairwise_term_nonpos hanti hi hj
  have hstrict_term : (scanCost a - scanCost b) * (w a - w b) < 0 := by
    simp only [scanCost]
    have hc : (a : ℝ) - b < 0 := by
      have : (a : ℝ) < b := by exact_mod_cast hab
      linarith
    exact mul_neg_of_neg_of_pos hc (by linarith)
  have hstrict_inner : ∑ j ∈ positions M, (scanCost a - scanCost j) * (w a - w j) < 0 := by
    have hle : ∀ j ∈ positions M, (scanCost a - scanCost j) * (w a - w j) ≤ 0 :=
      fun j hj => pairwise_term_nonpos hanti ha hj
    have hlt : ∑ j ∈ positions M, (scanCost a - scanCost j) * (w a - w j)
        < ∑ _j ∈ positions M, (0 : ℝ) :=
      Finset.sum_lt_sum (fun j hj => by simpa using hle j hj) ⟨b, hb, by simpa using hstrict_term⟩
    simpa using hlt
  have hdouble : ∑ i ∈ positions M, ∑ j ∈ positions M,
      (scanCost i - scanCost j) * (w i - w j) < 0 := by
    have hlt : ∑ i ∈ positions M, (∑ j ∈ positions M, (scanCost i - scanCost j) * (w i - w j))
        < ∑ _i ∈ positions M, (0 : ℝ) :=
      Finset.sum_lt_sum (fun i hi => by simpa using hinner_nonpos i hi)
        ⟨a, ha, by simpa using hstrict_inner⟩
    simpa using hlt
  -- convert via the identity
  have hid := chebyshev_double_sum (positions M) scanCost w
  rw [card_positions] at hid
  have hsumc : ∑ i ∈ positions M, scanCost i = (M : ℝ) * ((M : ℝ) + 1) / 2 := by
    simpa [scanCost] using sum_positions M
  have hsumw : ∑ i ∈ positions M, w i = 1 := htot
  rw [hsumc, hsumw] at hid
  have hdefect : (M : ℝ) * EC M scanCost w - (M : ℝ) * ((M : ℝ) + 1) / 2 * 1 < 0 := by
    rw [EC]
    nlinarith [hid, hdouble]
  rw [baselineC0]
  nlinarith [hdefect, hMR]
