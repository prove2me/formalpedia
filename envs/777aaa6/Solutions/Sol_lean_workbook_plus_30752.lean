-- Prove2me | solution 1 for lean_workbook_plus_30752
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:25:56.306718+00:00
-- url     : https://prove2.me/submissions/8c80a80b-a75b-4e76-af43-29851ed5710a

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 1 ≤ n) : √n ≤ n := by
  have h1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h0 : (0:ℝ) ≤ n := by linarith
  calc √(n:ℝ) ≤ √((n:ℝ)^2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = n := Real.sqrt_sq h0
