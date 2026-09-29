-- Prove2me | solution 1 for lean_workbook_plus_40274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:32.840992+00:00
-- url     : https://prove2.me/submissions/282ee4c0-e0bc-4592-a595-77ef8e26ee36

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c: ℝ) : a * b ≤ (a ^ 2 + b ^ 2) / 2 ∧ a * c ≤ (a ^ 2 + c ^ 2) / 2 ∧ b * c ≤ (b ^ 2 + c ^ 2) / 2 := by
  constructor
  · nlinarith only [sq_nonneg (a-b)]
  constructor
  · nlinarith only [sq_nonneg (a-c)]
  · nlinarith only [sq_nonneg (b-c)]
