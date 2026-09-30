-- Prove2me | solution 1 for lean_workbook_plus_70519
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:58.001751+00:00
-- url     : https://prove2.me/submissions/f8be6bfe-81bf-4858-9b0e-aa2b6c14472f

import Mathlib.Analysis.Complex.Basic

theorem solution (k : ℕ) (h : 1 < k) : (1 : ℝ) + 1 / k + (1 / k ^ 2) + 1 / k ^ 3 < k / (k - 1) := by
  have hk : (2:ℝ) ≤ k := by exact_mod_cast h
  have hk0 : (0:ℝ) < k := by linarith
  have hk1 : (0:ℝ) < (k:ℝ) - 1 := by linarith
  rw [lt_div_iff₀ hk1]
  have hpos : (0:ℝ) < 1 / (k:ℝ) ^ 3 := by positivity
  have key : ((1 : ℝ) + 1 / k + (1 / k ^ 2) + 1 / k ^ 3) * ((k:ℝ) - 1) = k - 1 / (k:ℝ) ^ 3 := by
    field_simp
    ring
  rw [key]
  linarith
