-- Prove2me | solution 1 for lean_workbook_plus_8064
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:33.212904+00:00
-- url     : https://prove2.me/submissions/f2147bee-0201-4ab0-a589-cef61b2c2b4e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z s q : ℝ) (hx : x + y + z = s) (hy : x*y + y*z + z*x = q) : s^2 ≥ 3*q := by
  subst s
  subst q
  nlinarith only [sq_nonneg (x-y),sq_nonneg (y-z),sq_nonneg (z-x)]
