-- Prove2me | solution 1 for lean_workbook_plus_80965
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:46.505874+00:00
-- url     : https://prove2.me/submissions/ab6428d5-7021-4541-8755-74d4a557fcde

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (h : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0)
    (h1 : (a + 1) * (b + 1) * (c + 1) = 8) : a * b * c ≤ 1 := by
  rcases h with ⟨ha0, hb0, hc0⟩
  have ha : 4*a ≤ (a+1)^2 := by nlinarith [sq_nonneg (a-1)]
  have hb : 4*b ≤ (b+1)^2 := by nlinarith [sq_nonneg (b-1)]
  have hc : 4*c ≤ (c+1)^2 := by nlinarith [sq_nonneg (c-1)]
  have hab := mul_le_mul ha hb (by positivity : 0 ≤ 4*b) (sq_nonneg (a+1))
  have habc := mul_le_mul hab hc (by positivity : 0 ≤ 4*c)
    (by positivity : 0 ≤ (a+1)^2 * (b+1)^2)
  rw [← mul_pow, ← mul_pow, h1] at habc
  nlinarith
