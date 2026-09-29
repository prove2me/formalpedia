-- Prove2me | solution 1 for lean_workbook_plus_72215
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:04:53.410965+00:00
-- url     : https://prove2.me/submissions/04d04099-3d26-48d6-a447-5e10806aba49

import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ × ℝ → ℝ) (x y : ℝ) (fxy: f (x,y) = (x + y) / (1 + x*y)) : -1 < x ∧ x < 1 ∧ -1 < y ∧ y < 1 → -1 < f (x,y) ∧ f (x,y) < 1 := by
  intro h
  obtain ⟨hxl,hxu,hyl,hyu⟩ := h
  have hp := mul_pos (show 0 < 1+x by linarith) (show 0 < 1+y by linarith)
  have hm := mul_pos (show 0 < 1-x by linarith) (show 0 < 1-y by linarith)
  have hd : 0 < 1+x*y := by nlinarith
  rw [fxy]
  constructor
  · apply (lt_div_iff₀ hd).2; nlinarith
  · apply (div_lt_iff₀ hd).2; nlinarith
