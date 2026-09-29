-- Prove2me | solution 1 for lean_workbook_plus_18581
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:49.230095+00:00
-- url     : https://prove2.me/submissions/ffd42c2c-bea3-42bf-a078-c3c29e531204

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (b c a r s : ℝ)
  (h₀ : 0 < r ∧ 0 < s)
  (h₁ : b = c + r)
  (h₂ : a = c + r + s) :
  (a^3 - c^3 - 3 * b * (a - c) * (a + c - b) ≥ 0) ↔ (a^2 + a * c + c^2 - 3 * b * (a + c - b) ≥ 0) := by
  have hd : 0 < a-c := by linarith [h₀.1,h₀.2]
  have hi : a^3-c^3-3*b*(a-c)*(a+c-b) = (a-c)*(a^2+a*c+c^2-3*b*(a+c-b)) := by ring
  rw [hi]
  exact mul_nonneg_iff_of_pos_left hd
