-- Prove2me | solution 1 for lean_workbook_plus_69216
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:32:32.038892+00:00
-- url     : https://prove2.me/submissions/530c77f3-b10f-4f43-abf2-abc9b1585785

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 6) (α β : ℝ) :
    α * a + β * b ≤ Real.sqrt (6 * (α ^ 2 + β ^ 2)) := by
  apply Real.le_sqrt_of_sq_le
  have hm := congrArg (fun t : ℝ => t * (α ^ 2 + β ^ 2)) hab
  nlinarith [sq_nonneg (α * b - β * a)]

#print axioms solution
