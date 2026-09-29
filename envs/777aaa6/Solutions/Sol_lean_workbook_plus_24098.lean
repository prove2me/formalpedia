-- Prove2me | solution 1 for lean_workbook_plus_24098
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:18:41.43333+00:00
-- url     : https://prove2.me/submissions/4f7daba0-d98f-45e0-b5c7-a0ed9048521a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℂ) (hx : x^3998 = 0) : x^4002 = 0 := by
  (intros; simp_all)
