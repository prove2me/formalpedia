-- Prove2me | solution 1 for lean_workbook_plus_3423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:58:56.010606+00:00
-- url     : https://prove2.me/submissions/5e8c0a16-83e4-455e-beca-c54ef25e17f2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) (h : a^3 + b^3 = a - b) : a^2 + b^2 < 1   := by
  obtain ⟨ha, hb⟩ := hab
  have ha1 : a < 1 := by
    by_contra hn
    have ha1 : 1 ≤ a := le_of_not_gt hn
    have hA := mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg a)
    have hB := mul_nonneg (sub_nonneg.mpr ha1) ha.le
    nlinarith [pow_pos hb 3]
  have hba : b < a := by nlinarith [pow_pos ha 3, pow_pos hb 3]
  have hf : 0 < 1 + b ^ 2 - a * b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1.le) hb.le, sq_nonneg b]
  by_contra hn
  have hs : 0 ≤ a ^ 2 + b ^ 2 - 1 := by linarith
  nlinarith [mul_nonneg ha.le hs, mul_pos hb hf]
