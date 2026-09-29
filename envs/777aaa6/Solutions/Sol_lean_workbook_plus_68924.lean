-- Prove2me | solution 1 for lean_workbook_plus_68924
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:08.169418+00:00
-- url     : https://prove2.me/submissions/40370f10-5d41-43d0-9350-d458c7ecac9b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  ((a + b + c) / 3)^2 ≤ (a^2 + b^2 + c^2) / 3 := by
  nlinarith only [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
