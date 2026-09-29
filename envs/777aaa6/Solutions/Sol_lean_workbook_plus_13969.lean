-- Prove2me | solution 1 for lean_workbook_plus_13969
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:10.395986+00:00
-- url     : https://prove2.me/submissions/55c1fd4e-5865-4b88-9987-cc61a327930d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) : (-1 * (5 * x - 6) / 25) + (1 * (5 * x - 6) / 25) = 0 := by
  (intros; linarith)
