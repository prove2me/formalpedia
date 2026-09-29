-- Prove2me | solution 1 for lean_workbook_plus_73843
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:10.985171+00:00
-- url     : https://prove2.me/submissions/9c60bfac-2164-4fef-abd8-7c17f12b1538

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c x y z : ℝ) (h1 : a^2 * c = x) (h2 : b^2 * a = y) (h3 : c^2 * b = z) : x^2 + y^2 + z^2 ≥ x * y + y * z + z * x := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
