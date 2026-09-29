-- Prove2me | solution 1 for lean_workbook_plus_31306
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:37:52.404443+00:00
-- url     : https://prove2.me/submissions/9399e7c8-b5a9-401a-8e57-7ce188980353

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3) ≥ 3 * (a + 1) * (b + 1) * (c + 1) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have hpos_c : (0 : ℝ) ≤ c := by first | positivity | linarith
  have h : (0 : ℝ) ≤ (4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3)) - (3 * (a + 1) * (b + 1) * (c + 1)) := by
    calc
      0 ≤ (2 : ℝ) * (1) * ((1 + ((-1) * a)))^2 + ((7 / 2) : ℝ) * (1) * ((1 + ((-1) * b)))^2 + ((7 / 2) : ℝ) * (1) * ((1 + ((-1) * c)))^2 + ((3 / 2) : ℝ) * (1) * ((b + ((-1) * c)))^2 + ((3 / 2) : ℝ) * (c) * ((1 + ((-1) * a)))^2 + ((5 / 2) : ℝ) * (c) * ((1 + ((-1) * c)))^2 + ((3 / 2) : ℝ) * (c) * ((a + ((-1) * c)))^2 + ((3 / 2) : ℝ) * (b) * ((1 + ((-1) * a)))^2 + ((5 / 2) : ℝ) * (b) * ((1 + ((-1) * b)))^2 + ((3 / 2) : ℝ) * (b) * ((a + ((-1) * b)))^2 + (1 : ℝ) * (a) * ((1 + ((-1) * a)))^2 + ((3 / 2) : ℝ) * (a) * ((a + ((-1) * b)))^2 + ((3 / 2) : ℝ) * (a) * ((a + ((-1) * c)))^2 + ((3 / 2) : ℝ) * (a) * ((b + ((-1) * c)))^2 := by positivity
      _ = (4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3)) - (3 * (a + 1) * (b + 1) * (c + 1)) := by ring
  exact sub_nonneg.mp h
