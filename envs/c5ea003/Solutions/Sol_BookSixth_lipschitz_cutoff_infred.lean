-- Prove2me | solution 1 for BookSixth.lipschitz_cutoff_infred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T23:02:45.642994+00:00
-- url     : https://prove2.me/submissions/7d4e41e4-b81e-4c5a-a534-143c3c78ecba

import Mathlib
import Definitions.Def_BookSixth

noncomputable section

open scoped BigOperators
open BookSixth

/-- **A Lipschitz cut-off with a finite, motion-independent constant.**

The witness is Mathlib's thickened indicator applied to the closed `d`-neighbourhood
of `K`:

    chi x = (thickenedIndicator hd (Metric.cthickening d K) x : ℝ≥0)

Because the indicator is `1` on its own set and `0` outside a further `d`-neighbourhood,
it is `1` on the closed `d`-thickening of `K` and `0` outside the closed `2*d`-thickening.

The key point is that `thickenedIndicator` performs its arithmetic in `ℝ≥0∞` on
`infEDist`, so it never needs `K` to be inhabited: `infEDist x ∅ = ∞` and the
construction still gives the identically zero cut-off.  Compactness of `K` is
therefore not needed at all. -/
theorem solution {K : Set Space3} (hK : IsCompact K) {d : ℝ} (hd : 0 < d) :
    ∃ chi : Space3 → ℝ,
      (∀ x, 0 ≤ chi x ∧ chi x ≤ 1) ∧
      (∀ x, x ∈ Metric.cthickening d K → chi x = 1) ∧
      (∀ x, x ∉ Metric.cthickening (2 * d) K → chi x = 0) ∧
      LipschitzWith (Real.toNNReal (1 / d)) chi := by
  classical
  -- A further `d`-neighbourhood of the closed `d`-neighbourhood of `K` is
  -- contained in the closed `2*d`-neighbourhood of `K`.
  have hsub : Metric.thickening d (Metric.cthickening d K) ⊆ Metric.cthickening (2 * d) K :=
    (Metric.thickening_subset_cthickening d _).trans
      (by simpa only [two_mul, add_comm] using
        Metric.cthickening_cthickening_subset (le_of_lt hd) (le_of_lt hd) K)
  -- `Space3` must be named explicitly: leaving it to inference makes `0` and `1`
  -- in the numerics below ambiguous, since `thickenedIndicator` is polymorphic
  -- in its domain and the numerals have no type until `α` is fixed.
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
  · -- `thickenedIndicator` is `d`-Lipschitz into `ℝ≥0`, and `Real.toNNReal`
    -- is `1`-Lipschitz.  The composite constant is `d⁻¹ = (1/d)`.
    -- The `: Space3` annotation is required: without it the domain of
    -- `thickenedIndicator` stays a metavariable and the numerals in the
    -- `LipschitzWith` argument have no type.
    have h1 : LipschitzWith (Real.toNNReal d)⁻¹
        (fun x : Space3 => thickenedIndicator hd (Metric.cthickening d K) x) :=
      lipschitzWith_thickenedIndicator hd (Metric.cthickening d K)
    -- `Real.toNNReal : ℝ → ℝ≥0`, so `1 / d` is real division and the result is
    -- already `ℝ≥0`; the extra ascription is redundant.  `Real.toNNReal_inv`
    -- concludes on `x⁻¹`, so `1 / d` must be rewritten *into* `d⁻¹` first.
    have hK : Real.toNNReal (1 / d) = (Real.toNNReal d)⁻¹ := by
      rw [one_div, Real.toNNReal_inv]
    have hcomp : LipschitzWith ((Real.toNNReal d)⁻¹)
        (fun x : Space3 => (thickenedIndicator hd (Metric.cthickening d K) x : ℝ)) := by
      -- `PseudoMetricSpace ℝ≥0` is the induced subtype metric, so `edist` on
      -- `ℝ≥0` is *definitionally* the `ℝ`-valued `edist` of the coerced reals
      -- (the remote verifier confirmed this: it printed the coerced forms on
      -- both sides).  So the `ℝ`-valued witness in the goal is literally the
      -- coercion of `h1`'s function and `exact h1` closes it, with no
      -- Lipschitz-with-congruence or `Function.comp_apply` step needed.
      exact h1
    -- The goal's constant is `Real.toNNReal (1 / d)`, which is exactly the LHS of
    -- `hK`, so `hK` rewrites it forward into `(Real.toNNReal d)⁻¹`.
    rw [hK]
    exact hcomp
