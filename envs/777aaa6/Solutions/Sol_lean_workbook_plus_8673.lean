-- Prove2me | solution 1 for lean_workbook_plus_8673
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:10.489499+00:00
-- url     : https://prove2.me/submissions/6550a490-b877-4dcd-a02b-df8071714547

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 3*x + 5*y = 7) : 9*x^2 + 25*y^2 ≤ 49 := by
  nlinarith [mul_nonneg hx hy]
