-- Prove2me | solution 1 for lean_workbook_plus_71539
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:54.311148+00:00
-- url     : https://prove2.me/submissions/efd90fc8-4824-4637-b45a-18f1d4fa44c7

import Mathlib

theorem solution (a b : ℝ) (hab : a + b > 2) :
    (a + b) ^ 2 / (a + b - 2) ≥ 8 ↔ (a + b - 4) ^ 2 ≥ 0 := by
  have hd : 0 < a + b - 2 := by linarith
  constructor
  · intro _
    exact sq_nonneg _
  · intro hs
    apply (le_div_iff₀ hd).mpr
    nlinarith

#print axioms solution
