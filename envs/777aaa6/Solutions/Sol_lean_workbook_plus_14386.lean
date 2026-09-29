-- Prove2me | solution 1 for lean_workbook_plus_14386
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:13.211572+00:00
-- url     : https://prove2.me/submissions/48967d5d-1af3-46a3-857b-e2774fafb850

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2 ≥ a ^ 3 * c ^ 2 * b + b ^ 3 * a ^ 2 * c + c ^ 3 * b ^ 2 * a := by
  intros
  have h : (0 : ℝ) ≤ (a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2) - (a ^ 3 * c ^ 2 * b + b ^ 3 * a ^ 2 * c + c ^ 3 * b ^ 2 * a) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (c ^ 2))))^2 + ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = (a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2) - (a ^ 3 * c ^ 2 * b + b ^ 3 * a ^ 2 * c + c ^ 3 * b ^ 2 * a) := by ring
  exact sub_nonneg.mp h
