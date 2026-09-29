-- Prove2me | solution 1 for lean_workbook_plus_23968
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:16:02.5475+00:00
-- url     : https://prove2.me/submissions/0f0feaf3-0613-4ef1-b69d-c367f8338b29

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h : a < -2016) : a^2 + 2017*a + 2017 > 1 := by
  (intros; nlinarith [sq_nonneg (a)])
