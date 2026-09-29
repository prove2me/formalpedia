-- Prove2me | solution 1 for lean_workbook_plus_43824
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:53.275793+00:00
-- url     : https://prove2.me/submissions/615e716c-6565-42b8-a67c-3165e7df318b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x+y+z)^2 >= 3*(x*y+y*z+z*x) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
