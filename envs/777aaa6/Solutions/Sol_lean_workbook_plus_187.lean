-- Prove2me | solution 1 for lean_workbook_plus_187
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:09.214812+00:00
-- url     : https://prove2.me/submissions/ea1005ac-2439-4dbb-b435-f9239bd9cabc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3 := by
  (intros; linarith)
