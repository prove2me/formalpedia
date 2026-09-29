-- Prove2me | solution 1 for lean_workbook_plus_6591
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:46.371667+00:00
-- url     : https://prove2.me/submissions/23d004c1-8494-456f-aeb8-71d025e91b83

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx: x >= 2) : x + 1/(x+2) >= 9/4 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
