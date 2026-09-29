-- Prove2me | solution 1 for lean_workbook_plus_37630
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:12:47.950809+00:00
-- url     : https://prove2.me/submissions/bd8b7de4-a95a-4485-8f47-8af72770a32b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b ≠ 1) (h : (1 / (a * (1 + b))) + (1 / (b * (1 + a))) = 2 / (1 + a * b)) : a + b ≥ 2 := by
  clear hab
  have hs : 0 < a+b := by linarith
  have hd1 : 1+a ≠ 0 := by positivity
  have hd2 : 1+b ≠ 0 := by positivity
  have hd3 : 1+a*b ≠ 0 := by positivity
  field_simp [ne_of_gt ha, ne_of_gt hb, hd1, hd2, hd3] at h
  have he : (a+b)*(1-a*b)=0 := by nlinarith
  have hp : a*b=1 := by
    rcases mul_eq_zero.mp he with hn | hn
    · exact False.elim ((ne_of_gt hs) hn)
    · linarith
  by_contra hn
  have hgap := mul_pos (show 0 < 2-(a+b) by linarith) (show 0 < 2+(a+b) by linarith)
  nlinarith [sq_nonneg (a-b)]
