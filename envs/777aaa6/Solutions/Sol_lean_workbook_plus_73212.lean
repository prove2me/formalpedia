-- Prove2me | solution 1 for lean_workbook_plus_73212
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:30:20.691493+00:00
-- url     : https://prove2.me/submissions/dfba5ec9-5587-40c8-b602-69540281af61

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    (b * c ^ 3 + c * a ^ 3 + a * b ^ 3) ^ 2 ≥
      3 * a * b * c * (a ^ 2 * c ^ 3 + a ^ 3 * b ^ 2 + b ^ 3 * c ^ 2) := by
  nlinarith only [sq_nonneg (b * c ^ 3 - c * a ^ 3),
    sq_nonneg (c * a ^ 3 - a * b ^ 3), sq_nonneg (a * b ^ 3 - b * c ^ 3)]
