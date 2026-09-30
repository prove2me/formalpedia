-- Prove2me | solution 1 for lean_workbook_plus_81773
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:14:07.359847+00:00
-- url     : https://prove2.me/submissions/10611507-93e5-433d-97a4-883f07d8422a

import Mathlib

theorem solution : ∀ x y : ℝ, x^2 + x*y + y^2 - x - y + 1 ≥ 2/3 := by
  intro x y
  nlinarith only [sq_nonneg (x - y), sq_nonneg (x + y - 2/3)]
