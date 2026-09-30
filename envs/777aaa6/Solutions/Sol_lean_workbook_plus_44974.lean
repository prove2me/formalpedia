-- Prove2me | solution 1 for lean_workbook_plus_44974
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:21:53.145546+00:00
-- url     : https://prove2.me/submissions/52eef2ee-91c1-4c5e-a55b-f8661cc2aa00

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : n > 0) : (n + 1/2) < Real.sqrt (n^2 + n + 1) ∧ Real.sqrt (n^2 + n + 1) < n + 1 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · rw [Real.lt_sqrt (by positivity)]
    nlinarith
  · rw [Real.sqrt_lt' (by positivity)]
    nlinarith
