-- Prove2me | solution 1 for lean_workbook_plus_11427
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:26.841615+00:00
-- url     : https://prove2.me/submissions/df6e5cce-c6f0-4466-bd97-75e28cdeacea

import Mathlib.Analysis.Complex.Basic

theorem solution (k : ℕ) (h : 1 ≤ k) : (1 : ℝ) + 1/k ≤ 2 := by
  have hk : (1:ℝ) ≤ k := by exact_mod_cast h
  have : 1 / (k:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hk
  linarith
