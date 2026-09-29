-- Prove2me | solution 1 for lean_workbook_plus_384
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:09.554042+00:00
-- url     : https://prove2.me/submissions/0e7096b5-744e-4195-a2be-a1273e8024d7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) ≥ 3 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) + 3 * a * b * c * (a + b + c) := by
  intros
  have h : (0 : ℝ) ≤ (2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) - (3 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) + 3 * a * b * c * (a + b + c)) := by
    calc
      0 ≤ ((3 / 2) : ℝ) * (((c ^ 2) + ((-1) * b * c)))^2 + ((1 / 2) : ℝ) * (((c ^ 2) + ((-1) * a * b)))^2 + (1 : ℝ) * (((b * c) + ((-1) * a * c)))^2 + (1 : ℝ) * (((b * c) + ((-1) * a * b)))^2 + ((1 / 2) : ℝ) * ((((-1) * (a ^ 2)) + (b * c)))^2 + ((1 / 2) : ℝ) * (((b ^ 2) + ((-1) * a * c)))^2 + ((3 / 2) : ℝ) * (((b ^ 2) + ((-1) * a * b)))^2 + (1 : ℝ) * (((a * c) + ((-1) * a * b)))^2 + ((3 / 2) : ℝ) * ((((-1) * (a ^ 2)) + (a * c)))^2 := by positivity
      _ = (2 * (a ^ 4 + b ^ 4 + c ^ 4) + 4 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)) - (3 * (a ^ 3 * c + b ^ 3 * a + c ^ 3 * b) + 3 * a * b * c * (a + b + c)) := by ring
  exact sub_nonneg.mp h
