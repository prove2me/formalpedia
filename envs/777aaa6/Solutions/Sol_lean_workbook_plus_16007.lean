-- Prove2me | solution 1 for lean_workbook_plus_16007
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:01.193709+00:00
-- url     : https://prove2.me/submissions/b5cadb40-7e65-4ffe-8238-20a597ae0d61

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ a b : ℝ, (a * b ≠ 0) → 1 / (2 * a ^ 2) + 1 / (2 * b ^ 2) ≥ 1 / |a * b| := by
  intro a b hab
  have ha : a≠0 := (mul_ne_zero_iff.mp hab).1
  have hb : b≠0 := (mul_ne_zero_iff.mp hab).2
  have hp : 0 < |a| := abs_pos.mpr ha
  have hq : 0 < |b| := abs_pos.mpr hb
  have hi : 1/(2*(abs a)^2)+1/(2*(abs b)^2)-1/(abs a*abs b)=(abs a-abs b)^2/(2*(abs a)^2*(abs b)^2) := by field_simp; ring
  have hn : 0≤(abs a-abs b)^2/(2*(abs a)^2*(abs b)^2) := by positivity
  simp only [sq_abs] at hi hn
  rw [abs_mul]
  linarith
