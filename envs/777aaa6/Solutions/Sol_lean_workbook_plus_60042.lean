-- Prove2me | solution 1 for lean_workbook_plus_60042
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:24.421071+00:00
-- url     : https://prove2.me/submissions/a3763b24-4420-4c26-9e78-71b7f1152ab8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ x : ℝ, 0 < x ∧ x < 1 → 0 < 20 * x^3 ∧ 20 * x^3 < 20 * x := by
  intro x h
  have hx : 0 < x := h.1
  have hx2 : x^2 < 1 := by nlinarith [mul_pos h.1 (sub_pos.mpr h.2)]
  have hp := mul_lt_mul_of_pos_left hx2 h.1
  constructor
  · positivity
  · nlinarith
