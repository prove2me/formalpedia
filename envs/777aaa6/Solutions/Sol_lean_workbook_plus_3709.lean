-- Prove2me | solution 1 for lean_workbook_plus_3709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:30:20.724237+00:00
-- url     : https://prove2.me/submissions/bc0b160a-2358-4529-95fa-15f371b62129

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (a^2 + a * c + c^2) := by
  intros
  have h : (0 : ℝ) ≤ (3 * (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) - ((a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (a^2 + a * c + c^2)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * c * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * a * (c ^ 2))))^2 + (1 : ℝ) * (((b * (c ^ 2)) + ((-1) * a * b * c)))^2 + (1 : ℝ) * (((c * (b ^ 2)) + ((-1) * a * b * c)))^2 + ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (b ^ 2))))^2 + (1 : ℝ) * (((a * (c ^ 2)) + ((-1) * a * b * c)))^2 + ((1 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 + (1 : ℝ) * ((((-1) * a * (b ^ 2)) + (a * b * c)))^2 + (1 : ℝ) * ((((-1) * c * (a ^ 2)) + (a * b * c)))^2 + (1 : ℝ) * ((((-1) * b * (a ^ 2)) + (a * b * c)))^2 + ((1 / 2) : ℝ) * (((a * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((c * (a ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = (3 * (a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) - ((a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (a^2 + a * c + c^2)) := by ring
  exact sub_nonneg.mp h
