-- Prove2me | solution 1 for lean_workbook_plus_63838
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:50.601406+00:00
-- url     : https://prove2.me/submissions/2bef491a-3747-4977-9698-a298f0d7871f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx: x ≥ 3) : (x^2 / (x + 3)) ≥ 3 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
