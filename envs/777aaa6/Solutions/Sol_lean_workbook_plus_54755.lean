-- Prove2me | solution 1 for lean_workbook_plus_54755
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:09:23.301083+00:00
-- url     : https://prove2.me/submissions/9962347e-f648-4aee-abd9-810969b16078

import Mathlib.Analysis.Complex.Basic

theorem solution (y : ℝ) (k : ℕ) (_hk : 1 ≤ k) (_hy : -1 ≤ y) : (y + 1) ^ k ≥ k * y + 1 := by
  have := one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ y) k
  rw [add_comm 1 y] at this
  linarith
