-- Prove2me | solution 1 for lean_workbook_plus_42117
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:45:57.754734+00:00
-- url     : https://prove2.me/submissions/9ed530fe-60bb-4fc3-a41f-eb01594b5cc9

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h : b - c ≥ a - b ∧ a - b ≥ 0) :
  3 * (a^2 * b + b^2 * a + b^2 * c + c^2 * b + a^2 * c + c^2 * a) ≥
    2 * (a^3 + b^3 + c^3) + 12 * a * b * c := by
  have h1 : 0 ≤ 2*a-b-c := by linarith [h.1,h.2]
  have h2 : 0 ≤ 2*b-a-c := by linarith [h.1]
  have h3 : 0 ≤ a+b-2*c := by linarith [h.1,h.2]
  have hp := mul_nonneg (mul_nonneg h1 h2) h3
  nlinarith only [hp]
