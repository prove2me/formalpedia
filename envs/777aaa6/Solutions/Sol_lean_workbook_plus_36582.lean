-- Prove2me | solution 1 for lean_workbook_plus_36582
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:35.328984+00:00
-- url     : https://prove2.me/submissions/9b24ba9e-1b3b-49d0-bda9-81ab62ac9708

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b^2 / a = b + a^2 / b) : a = b := by
  field_simp [ha,hb] at hab
  have hf : (a-b)*(a^2+b^2)=0 := by nlinarith
  have hp : 0 < a^2+b^2 := by nlinarith [sq_pos_of_ne_zero ha,sq_nonneg b]
  have hz := (mul_eq_zero.mp hf).resolve_right (ne_of_gt hp)
  linarith
