-- Prove2me | solution 1 for lean_workbook_plus_7381
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:26.993227+00:00
-- url     : https://prove2.me/submissions/c7b1d742-5ded-4210-98e7-2eb3284262cb

import Mathlib.Analysis.Complex.Basic

theorem solution (x y : ℝ) : ‖x - y‖ * ‖x + y‖ ≤ ‖x‖^2 + ‖y‖^2 := by
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← abs_mul]
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
