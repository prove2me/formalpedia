-- Prove2me | solution 1 for lean_workbook_plus_5108
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:50:03.207246+00:00
-- url     : https://prove2.me/submissions/15ebcfa2-5541-42ea-9b02-9c03af95c326

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : a^2 <= 1 ∧ b^2 <= 1 ∧ c^2 <= 1 := by
  constructor
  · nlinarith [sq_nonneg b,sq_nonneg c]
  · constructor <;> nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c]
