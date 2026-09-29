-- Prove2me | solution 1 for lean_workbook_plus_51484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:49:46.149234+00:00
-- url     : https://prove2.me/submissions/e6280166-3360-4e3d-bdf3-ba71e2605adf

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
theorem solution (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a + b ≥ 1 / 2 * (c + d)) (h : a^2 + b^2 = 1 / 2 * (c^2 + d^2)) : a^4 + a^2 * b^2 + b^4 ≤ 1 / 3 * (c^4 + c^2 * d^2 + d^4)    := by
  have hs := congrArg (fun t : ℝ => t^2) h
  nlinarith only [hs, sq_nonneg (a*b), sq_nonneg (c^2-d^2)]
