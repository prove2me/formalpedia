-- Prove2me | solution 1 for lean_workbook_plus_48528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:58.460788+00:00
-- url     : https://prove2.me/submissions/8260d05d-d6ff-41ae-b7e8-a36f70c48c7d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a^2 * b^2 * c^2 * (a^2 + b^2 + c^2) ≥ a^3 * b^3 * c^2 + a^3 * b^2 * c^3 + a^2 * b^3 * c^3 := by
  intros
  have h : (0 : ℝ) ≤ (a^2 * b^2 * c^2 * (a^2 + b^2 + c^2)) - (a^3 * b^3 * c^2 + a^3 * b^2 * c^3 + a^2 * b^3 * c^3) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((a * b * (c ^ 2)) + ((-1) * a * c * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((a * b * (c ^ 2)) + ((-1) * b * c * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((a * c * (b ^ 2)) + ((-1) * b * c * (a ^ 2))))^2 := by positivity
      _ = (a^2 * b^2 * c^2 * (a^2 + b^2 + c^2)) - (a^3 * b^3 * c^2 + a^3 * b^2 * c^3 + a^2 * b^3 * c^3) := by ring
  exact sub_nonneg.mp h
