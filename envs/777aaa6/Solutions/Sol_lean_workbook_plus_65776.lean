-- Prove2me | solution 1 for lean_workbook_plus_65776
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:54:18.497885+00:00
-- url     : https://prove2.me/submissions/52fbe227-bd07-4f74-909f-a4edb2faadaf

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem quadratic_minimum_identity (x y : ℝ) :
    x ^ 2 + 2 * x * y + 3 * y ^ 2 + 2 * x + 6 * y + 4 =
      (x + y + 1) ^ 2 + 2 * (y + 1) ^ 2 + 1 := by ring

theorem unique_quadratic_minimizer (x y : ℝ) :
    x ^ 2 + 2 * x * y + 3 * y ^ 2 + 2 * x + 6 * y + 4 = 1 ↔
      x = 0 ∧ y = -1 := by
  rw [quadratic_minimum_identity]
  constructor
  · intro h
    have hy : y = -1 := by nlinarith [sq_nonneg (x + y + 1), sq_nonneg (y + 1)]
    exact ⟨by rw [hy] at h; nlinarith [sq_nonneg x], hy⟩
  · rintro ⟨rfl, rfl⟩
    ring

theorem solution (x y : ℝ) :
    x ^ 2 + 2 * x * y + 3 * y ^ 2 + 2 * x + 6 * y + 4 ≥ 1 := by
  rw [quadratic_minimum_identity]
  nlinarith [sq_nonneg (x + y + 1), sq_nonneg (y + 1)]
