-- Prove2me | solution 1 for lean_workbook_plus_26277
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:17:53.274822+00:00
-- url     : https://prove2.me/submissions/95bfc39c-d466-4a70-8d1c-6aac8abb34fc

import Mathlib.Analysis.Complex.Basic

/-- The inequality holds for all real `a b c` (the hypothesis `h` is not needed):
`a^4 + b^4 + c^4 + 2abc(a+b+c) = ((a^2-b^2)^2 + (b^2-c^2)^2 + (c^2-a^2)^2)/2 + (ab+bc+ca)^2`. -/
theorem solution (a b c : ℝ) (h : a ^ 3 * b + b ^ 3 * c + c ^ 3 * a = 0) :
  a ^ 4 + b ^ 4 + c ^ 4 + 2 * a * b * c * (a + b + c) ≥ 0 := by
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2),
    sq_nonneg (a * b + b * c + c * a)]
