-- Prove2me | solution 1 for lean_workbook_plus_36363
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:27.989671+00:00
-- url     : https://prove2.me/submissions/234b5fd5-55a7-4030-8b9e-5c28c62f06fe

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c x : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a * b + b * c + c * a = 3) : (x ^ 2 * a ^ 2 + 1) * (x ^ 2 * b ^ 2 + 1) * (x ^ 2 * c ^ 2 + 1) = (x ^ 3 * a * b * c - x * (a + b + c)) ^ 2 + (x ^ 2 * (a * b + b * c + c * a) - 1) ^ 2 ∧ (x ^ 2 * (a * b + b * c + c * a) - 1) ^ 2 ≤ (x ^ 2 * a ^ 2 + 1) * (x ^ 2 * b ^ 2 + 1) * (x ^ 2 * c ^ 2 + 1) := by
  constructor
  · ring
  · nlinarith only [sq_nonneg (x^3*a*b*c-x*(a+b+c))]
