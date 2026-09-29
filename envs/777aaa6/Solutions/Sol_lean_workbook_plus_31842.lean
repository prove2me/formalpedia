-- Prove2me | solution 1 for lean_workbook_plus_31842
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:05:27.745219+00:00
-- url     : https://prove2.me/submissions/b0dc3ac5-8e26-495a-9872-ba268be5778c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / b + b / c + c / a >= (a + b) / (b + c) + (b + c) / (a + b) + 1   := by
  have hp : 0 ≤ (b + c) * (a * b - b * c) ^ 2 + a * (a * c - b ^ 2) ^ 2 := by positivity
  field_simp
  nlinarith only [hp]
