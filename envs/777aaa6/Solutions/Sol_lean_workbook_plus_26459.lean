-- Prove2me | solution 1 for lean_workbook_plus_26459
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:59:45.777802+00:00
-- url     : https://prove2.me/submissions/4d538202-6d0e-42c8-a62b-9c53dffcf2d4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b > c) (h : a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a)) (k : ℝ) (hk : k > 0) : (a + k * b) / c ≥ k / (k + 1)   := by
  clear hab
  have hA : 0 ≤ a + k ^ 2 * b := by positivity
  have hscaled := congrArg (fun t : ℝ => k ^ 2 * t) h
  have hsq : (k * (c - a - b)) ^ 2 ≤ (a + k ^ 2 * b) ^ 2 := by
    nlinarith [sq_nonneg (a - k ^ 2 * b)]
  have hbound := le_of_sq_le_sq hsq hA
  apply (div_le_div_iff₀ (show 0 < k + 1 by linarith) hc).2
  nlinarith
