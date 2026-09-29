-- Prove2me | solution 1 for lean_workbook_plus_37135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:33.265072+00:00
-- url     : https://prove2.me/submissions/f1ff5a70-abdc-4981-a266-fd20d1046bf1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) ≥ (5/16) * (a * b + b * c + c * a + 1)^2 := by
  intros
  have h : (0 : ℝ) ≤ ((a^2 + 1) * (b^2 + 1) * (c^2 + 1)) - ((5/16) * (a * b + b * c + c * a + 1)^2) := by
    calc
      0 ≤ ((903 / 8704) : ℝ) * ((1 + (2 * c)))^2 + ((903 / 8704) : ℝ) * ((1 + ((-2) * c)))^2 + ((807 / 8704) : ℝ) * ((1 + (2 * b)))^2 + ((807 / 8704) : ℝ) * ((1 + ((-2) * b)))^2 + ((21 / 544) : ℝ) * ((1 + ((-1) * b * c)))^2 + ((485 / 4352) : ℝ) * ((1 + ((-2) * b * c)))^2 + ((3 / 256) : ℝ) * ((1 + (2 * a)))^2 + ((3 / 256) : ℝ) * ((1 + ((-2) * a)))^2 + ((31 / 256) : ℝ) * ((1 + ((-2) * a * c)))^2 + ((111 / 4352) : ℝ) * ((c + ((-2) * b)))^2 + ((9 / 256) : ℝ) * ((c + ((-2) * a)))^2 + ((7 / 64) : ℝ) * ((c + ((-2) * a * b * c)))^2 + ((5 / 32) : ℝ) * ((b + ((-2) * a)))^2 + ((3 / 64) : ℝ) * (((b * c) + ((-2) * a * c)))^2 + ((5 / 32) : ℝ) * (((b * c) + ((-2) * a * b)))^2 + ((9 / 64) : ℝ) * ((a + ((-2) * a * b * c)))^2 + ((1 / 64) : ℝ) * (((a * c) + ((-2) * a * b)))^2 := by positivity
      _ = ((a^2 + 1) * (b^2 + 1) * (c^2 + 1)) - ((5/16) * (a * b + b * c + c * a + 1)^2) := by ring
  exact sub_nonneg.mp h
