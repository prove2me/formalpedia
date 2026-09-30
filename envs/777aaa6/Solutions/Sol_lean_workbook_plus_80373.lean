-- Prove2me | solution 1 for lean_workbook_plus_80373
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:47:19.592848+00:00
-- url     : https://prove2.me/submissions/e7977124-3dd4-4d33-b958-16d929271973

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (h₁ : a^3+b^3+c^3 = 64) (h₂ : a+b = 0) : c = 4 := by
  have hab : a = -b := by linarith only [h₂]
  rw [hab] at h₁
  have hfactor : (c-4)*(c^2+4*c+16) = 0 := by nlinarith only [h₁]
  have hpos : 0 < c^2+4*c+16 := by nlinarith only [sq_nonneg (c+2)]
  rcases mul_eq_zero.mp hfactor with hc | hc
  · linarith only [hc]
  · exact False.elim ((ne_of_gt hpos) hc)
