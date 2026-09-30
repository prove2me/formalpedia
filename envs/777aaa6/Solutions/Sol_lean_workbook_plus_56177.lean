-- Prove2me | solution 1 for lean_workbook_plus_56177
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:27:41.208934+00:00
-- url     : https://prove2.me/submissions/48b04846-99ea-4679-83cf-1bb3c0d3ab3d

import Mathlib.Analysis.Complex.Basic

theorem solution : (2010 / 2009 : ℝ) ^ (2009:ℕ) > 2 := by
  have hb : (1 : ℝ) + (2007 : ℕ) * (1 / 2009) ≤ (1 + 1 / 2009) ^ (2007 : ℕ) :=
    one_add_mul_le_pow (by norm_num) 2007
  have e : (2010 / 2009 : ℝ) ^ (2009 : ℕ) = (1 + 1 / 2009) ^ 2 * (1 + 1 / 2009) ^ (2007 : ℕ) := by
    rw [← pow_add]; norm_num
  rw [e]
  have hpos : (0 : ℝ) < (1 + 1 / 2009) ^ 2 := by positivity
  calc (2 : ℝ) < (1 + 1 / 2009) ^ 2 * ((1 : ℝ) + (2007 : ℕ) * (1 / 2009)) := by norm_num
    _ ≤ (1 + 1 / 2009) ^ 2 * (1 + 1 / 2009) ^ (2007 : ℕ) := by gcongr
