-- Prove2me | solution 1 for lean_workbook_plus_57336
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:26.198755+00:00
-- url     : https://prove2.me/submissions/31c51cc3-9582-40d0-83bf-6d28ffdd9bbb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) :
    14*(a^2 + b^2) + 53*a*b ≤ (81/4)*(a+b)^2 := by
  nlinarith [sq_nonneg (a - b)]
