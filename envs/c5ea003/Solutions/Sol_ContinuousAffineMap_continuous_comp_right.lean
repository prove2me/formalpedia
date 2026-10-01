-- Prove2me | solution 1 for ContinuousAffineMap.continuous_comp_right
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:07:20.947711+00:00
-- url     : https://prove2.me/submissions/04a0f06e-daa2-42f9-9669-2cfa4e206281

import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
  (g : ContinuousAffineMap ℝ E F) :
    Continuous (fun f : ContinuousAffineMap ℝ F G ↦ f.comp g) := by
  let C : NNReal := ⟨‖g‖ + 1, by positivity⟩
  apply (LipschitzWith.of_dist_le_mul (K := C) fun f h ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have heq : f.comp g - h.comp g = (f - h).comp g := by
    ext x
    simp
  rw [heq]
  calc
    ‖(f - h).comp g‖ ≤ ‖f - h‖ * ‖g‖ + ‖(f - h) 0‖ :=
      ContinuousAffineMap.norm_comp_le _ _
    _ ≤ ‖f - h‖ * ‖g‖ + ‖f - h‖ := by
      gcongr
      exact ContinuousAffineMap.norm_image_zero_le _
    _ = (C : ℝ) * ‖f - h‖ := by
      change _ = (‖g‖ + 1) * ‖f - h‖
      ring
