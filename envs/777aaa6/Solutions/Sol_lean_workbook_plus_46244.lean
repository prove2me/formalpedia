-- Prove2me | solution 1 for lean_workbook_plus_46244
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:24:58.360786+00:00
-- url     : https://prove2.me/submissions/1b4a6582-a272-4fbf-bfdf-b5419c90983a

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 1 < n) (c d : ℝ) (hcd : c + d = 1) :
  1 - 1 / n < c + d ∧ c + d < 1 + 1 / n := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpos : (0:ℝ) < 1 / (n:ℝ) := one_div_pos.mpr hn'
  constructor <;> linarith
