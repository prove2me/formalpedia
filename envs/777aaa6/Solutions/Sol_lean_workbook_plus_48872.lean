-- Prove2me | solution 1 for lean_workbook_plus_48872
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:33.343709+00:00
-- url     : https://prove2.me/submissions/6dc8cdf2-640f-4a85-a32a-306cc5f28ff2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : (x^2+y^2+z^2)/2 ≥ (x+y+z)^2/6 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
