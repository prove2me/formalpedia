-- Prove2me | solution 1 for lean_workbook_plus_11132
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:06:11.851147+00:00
-- url     : https://prove2.me/submissions/2be6ff5a-1c50-4aa5-8942-3456cbf9be3c

import Mathlib.Analysis.Complex.Basic

theorem solution (k : ℕ) (h : 1 < k) : (1:ℝ) / (Real.sqrt k + Real.sqrt (k - 1)) < (1:ℝ) / Real.sqrt k := by
  have hk : (1:ℝ) < k := by exact_mod_cast h
  have h1 : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 < Real.sqrt (k - 1) := Real.sqrt_pos.mpr (by linarith)
  apply one_div_lt_one_div_of_lt h1
  linarith
