-- Prove2me | solution 1 for lean_workbook_plus_47159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:23:11.439711+00:00
-- url     : https://prove2.me/submissions/b236cfde-a37b-4a03-8cd3-a1f9259816ad

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ (a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b) := by
  intros
  have h : (0 : ℝ) ≤ ((a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) - ((a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * c * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((b * (c ^ 2)) + ((-1) * a * (c ^ 2))))^2 + ((1 / 2) : ℝ) * (((c * (b ^ 2)) + ((-1) * a * (b ^ 2))))^2 + ((1 / 2) : ℝ) * (((a * (c ^ 2)) + ((-1) * c * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((a * (b ^ 2)) + ((-1) * b * (a ^ 2))))^2 + ((1 / 2) : ℝ) * (((c * (a ^ 2)) + ((-1) * b * (a ^ 2))))^2 := by positivity
      _ = ((a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2)) - ((a^2 + b * c) * (b^2 + c * a) * (c^2 + a * b)) := by ring
  exact sub_nonneg.mp h
