-- Prove2me | solution 1 for BookSixth.lipschitz_cutoff_infred_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T02:18:27.424853+00:00
-- url     : https://prove2.me/submissions/27cbb310-b72b-4125-a690-cbb6172fb6d3

import Mathlib
import Definitions.Def_BookSixth

noncomputable section

open scoped BigOperators
open BookSixth

/-- **A Lipschitz cut-off for an arbitrary nonempty set.**

This is the Proved theorem `BookSixth.lipschitz_cutoff_infred` with its
`IsCompact` hypothesis weakened to `K.Nonempty`. The witness is the same
Mathlib `thickenedIndicator` applied to the closed `d`-thickening of `K`, and
the proof is the same: `thickenedIndicator` does its arithmetic in `ℝ≥0∞` on
`infEDist`, so it never uses compactness, and with `infEDist x ∅ = ∞` it
would still produce the identically zero cut-off on the empty set. -/
theorem solution {K : Set Space3} (hK : K.Nonempty) {d : ℝ} (hd : 0 < d) :
    ∃ chi : Space3 → ℝ,
      (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x, x ∈ Metric.cthickening d K → chi x = 1) ∧
      (∀ x, x ∉ Metric.cthickening (2 * d) K → chi x = 0) ∧
      LipschitzWith (Real.toNNReal (1 / d)) chi := by
  classical
  have hsub : Metric.thickening d (Metric.cthickening d K) ⊆ Metric.cthickening (2 * d) K :=
    (Metric.thickening_subset_cthickening d _).trans
      (by simpa only [two_mul, add_comm] using
        Metric.cthickening_cthickening_subset (le_of_lt hd) (le_of_lt hd) K)
  refine ⟨fun x => (thickenedIndicator hd (Metric.cthickening d K) x : ℝ), ?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · exact NNReal.coe_nonneg _
    · exact NNReal.coe_le_one.mpr (thickenedIndicator_le_one hd _ _)
  · intro x hx
    exact NNReal.coe_inj.mpr (thickenedIndicator_one hd _ hx)
  · intro x hx
    have hx' : x ∉ Metric.thickening d (Metric.cthickening d K) := fun hmem => hx (hsub hmem)
    exact NNReal.coe_inj.mpr (thickenedIndicator_zero hd _ hx')
  · have h1 : LipschitzWith (Real.toNNReal d)⁻¹
        (fun x : Space3 => thickenedIndicator hd (Metric.cthickening d K) x) :=
      lipschitzWith_thickenedIndicator hd (Metric.cthickening d K)
    have hd' : Real.toNNReal (1 / d) = (Real.toNNReal d)⁻¹ := by
      rw [one_div, Real.toNNReal_inv]
    rw [hd']
    exact h1

end
