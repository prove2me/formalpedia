-- Prove2me | solution 1 for lean_workbook_plus_29736
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:07.014746+00:00
-- url     : https://prove2.me/submissions/46c1b245-006d-4c0c-9c30-688559121ab3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : x^4 + y^4 ≥ x * y * (x^2 + y^2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
