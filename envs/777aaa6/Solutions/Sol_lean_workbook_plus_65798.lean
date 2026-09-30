-- Prove2me | solution 1 for lean_workbook_plus_65798
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:19:06.99003+00:00
-- url     : https://prove2.me/submissions/87eff937-6855-4860-9f62-b12337513885

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

theorem solution (a b c : ℝ) :
    Real.sqrt (a ^ 2 + a * b + b ^ 2) + Real.sqrt (b ^ 2 + b * c + c ^ 2) =
    Real.sqrt (3 * (a + b) ^ 2 / 4 + (a - b) ^ 2 / 4) +
      Real.sqrt (3 * (b + c) ^ 2 / 4 + (b - c) ^ 2 / 4) := by
  congr 1 <;> congr 1 <;> ring
