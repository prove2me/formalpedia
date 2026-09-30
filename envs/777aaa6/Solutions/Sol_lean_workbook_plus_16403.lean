-- Prove2me | solution 1 for lean_workbook_plus_16403
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:17:09.385151+00:00
-- url     : https://prove2.me/submissions/8f0cf59c-46d6-4aa4-9c12-215a56fd5182

import Mathlib

theorem solution (f : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (h : ∀ x y, |f x - f y| ≤ c * |x - y|) : UniformContinuous f := by
  have hLip : LipschitzWith ⟨c, hc.le⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_mk] using h x y
  exact hLip.uniformContinuous

#print axioms solution
