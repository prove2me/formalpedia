-- Prove2me | solution 1 for lean_workbook_plus_4052
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:05:25.416401+00:00
-- url     : https://prove2.me/submissions/b53e7814-c2f4-48a3-8798-fb22a865b31f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a / b + b / c + c / a >= 3 + (c - a) ^ 2 / (b ^ 2 + a * b + b * c + c * a)   := by
  have hd : 0 < b ^ 2 + a * b + b * c + c * a := by positivity
  have hp : 0 ≤ (b + c) * (a * b - b * c) ^ 2 + a * (a * c - b ^ 2) ^ 2 := by positivity
  field_simp
  nlinarith only [hp]
