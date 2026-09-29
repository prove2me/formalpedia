-- Prove2me | solution 1 for lean_workbook_plus_18155
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:44:59.203538+00:00
-- url     : https://prove2.me/submissions/70dfc045-f209-4865-863a-20fe75e35497

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (a * (1 + b)) + 1 / (b * (1 + a)) = 2 / (1 + a * b) → a + b ≥ 2) := by
  intro heq
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have ha1 : 1+a ≠ 0 := by positivity
  have hb1 : 1+b ≠ 0 := by positivity
  have hab1 : 1+a*b ≠ 0 := by positivity
  field_simp at heq
  have hfac : (a+b)*(a*b-1)=0 := by nlinarith only [heq]
  have hab : a*b=1 := by
    rcases mul_eq_zero.mp hfac with hs | hp
    · linarith
    · linarith
  by_contra hn
  have hs : a+b < 2 := by linarith
  have hmul := mul_pos (by linarith : 0 < 2-a-b) (by linarith : 0 < 2+a+b)
  nlinarith [sq_nonneg (a-b)]
