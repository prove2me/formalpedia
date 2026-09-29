-- Prove2me | solution 1 for lean_workbook_plus_50239
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T19:37:31.889336+00:00
-- url     : https://prove2.me/submissions/2593b109-3a69-42d8-91d7-f48d3fa9d1f7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (a b : ℝ) (h : 2*a + 3*b = 60) : a * b ≤ 150   := by
  have hs := sq_nonneg (2 * a - 3 * b)
  nlinarith [sq_nonneg (2 * a + 3 * b - 60)]
