-- Prove2me | solution 1 for WhichFactorWall.binEntropy_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:38:54.758653+00:00
-- url     : https://prove2.me/submissions/0f858f99-b5fc-49c6-a888-62a097842101

import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
open WhichFactorWall Real Set in
theorem solution {δ p q : ℝ} (hδ : 0 < δ) (hp : p ∈ Icc δ (1 - δ))
    (hq : q ∈ Icc δ (1 - δ)) :
    |binEntropy p - binEntropy q| ≤ (log (1 - δ) - log δ) * |p - q| := by
  -- on `[δ, 1-δ]` the derivative `log(1-t) - log t` is bounded by `log(1-δ) - log δ`
  have hbound : ∀ t ∈ Icc δ (1 - δ), ‖deriv binEntropy t‖ ≤ log (1 - δ) - log δ := by
    rintro t ⟨ht1, ht2⟩
    rw [deriv_binEntropy, Real.norm_eq_abs, abs_le]
    have ha : log δ ≤ log t := log_le_log hδ ht1
    have hb : log t ≤ log (1 - δ) := log_le_log (by linarith) ht2
    have hc : log δ ≤ log (1 - t) := log_le_log hδ (by linarith)
    have hd : log (1 - t) ≤ log (1 - δ) := log_le_log (by linarith) (by linarith)
    constructor <;> linarith
  have hdiff : ∀ t ∈ Icc δ (1 - δ), DifferentiableAt ℝ binEntropy t := by
    rintro t ⟨ht1, ht2⟩
    exact differentiableAt_binEntropy (by linarith) (by linarith)
  have := (convex_Icc δ (1 - δ)).norm_image_sub_le_of_norm_deriv_le hdiff hbound hq hp
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact this
