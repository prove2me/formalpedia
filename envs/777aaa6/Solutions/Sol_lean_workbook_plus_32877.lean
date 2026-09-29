-- Prove2me | solution 1 for lean_workbook_plus_32877
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:19:21.873313+00:00
-- url     : https://prove2.me/submissions/99eb8b3c-5930-4b94-942c-635d8c43fff4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : (a + b) * (1 / a + 1 / b) ≤ 4 + max a b - min a b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hab0 : 0 < a*b := mul_pos ha0 hb0
  have he : (a+b)*(1/a+1/b) = 4+(a-b)^2/(a*b) := by
    field_simp [ne_of_gt ha0, ne_of_gt hb0]
    <;> ring
  rw [he]
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_left hab]
    have hd : 0 ≤ a*b-b+a := by nlinarith [mul_nonneg (show 0 ≤ a-1 by linarith) hb0.le]
    have hp := mul_nonneg (show 0 ≤ b-a by linarith) hd
    have hq : (a-b)^2/(a*b) ≤ b-a := (div_le_iff₀ hab0).2 (by nlinarith)
    linarith
  · rw [max_eq_left hba, min_eq_right hba]
    have hd : 0 ≤ a*b-a+b := by nlinarith [mul_nonneg (show 0 ≤ b-1 by linarith) ha0.le]
    have hp := mul_nonneg (show 0 ≤ a-b by linarith) hd
    have hq : (a-b)^2/(a*b) ≤ a-b := (div_le_iff₀ hab0).2 (by nlinarith)
    linarith
