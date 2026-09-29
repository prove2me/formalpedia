-- Prove2me | solution 1 for lean_workbook_plus_18941
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:25.777002+00:00
-- url     : https://prove2.me/submissions/2e21eacb-fd8e-4d33-8184-95361b9a8d77

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (h₁ : 0 < x ∧ 0 < y ∧ 0 < z) (h₂ : z > y) (h₃ : y > x) : (z - y) / x + (x - z) / y + (y - x) / z > 0 := by
  rcases h₁ with ⟨hx,hy,hz⟩
  have hzy : 0 < z-y := sub_pos.mpr h₂
  have hyx : 0 < y-x := sub_pos.mpr h₃
  have hzx : 0 < z-x := by linarith
  have hi : (z-y)/x+(x-z)/y+(y-x)/z = (z-y)*(y-x)*(z-x)/(x*y*z) := by field_simp; ring
  rw [hi]
  positivity
