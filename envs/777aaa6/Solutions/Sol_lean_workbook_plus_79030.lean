-- Prove2me | solution 1 for lean_workbook_plus_79030
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:36:34.365663+00:00
-- url     : https://prove2.me/submissions/01f24784-70a3-446e-afbb-32c6adf7f42f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a : ℝ) (ha : a^4 + a^3 = 1) : 2*a + 3 > 0 := by
  by_contra h
  have hn : (3/2 : ℝ) ≤ -a := by linarith
  have hs : (9/4 : ℝ) ≤ a^2 := by nlinarith [sq_nonneg (a+3/2)]
  have hc : (27/8 : ℝ) ≤ -a^3 := by
    have hm := mul_le_mul hs hn (by norm_num : (0 : ℝ) ≤ 3/2) (sq_nonneg a)
    nlinarith
  have hn1 : (1/2 : ℝ) ≤ -a-1 := by linarith
  have hm := mul_le_mul hc hn1 (by norm_num : (0 : ℝ) ≤ 1/2)
    (by linarith : 0 ≤ -a^3)
  nlinarith
