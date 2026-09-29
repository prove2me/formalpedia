-- Prove2me | solution 1 for lean_workbook_plus_30791
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:22.78832+00:00
-- url     : https://prove2.me/submissions/97b76bdb-dfda-4502-a9e8-9a50ae6008b8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) : (a^2 + 2005*b + 2006)*(b^2 + 2005*a + 2006) ≥ (2007*a + 2005)*(2007*b + 2005) := by
  intros
  have hpos_a : (0 : ℝ) ≤ a := by first | positivity | linarith
  have hpos_b : (0 : ℝ) ≤ b := by first | positivity | linarith
  have h : (0 : ℝ) ≤ ((a^2 + 2005*b + 2006)*(b^2 + 2005*a + 2006)) - ((2007*a + 2005)*(2007*b + 2005)) := by
    calc
      0 ≤ ((6015 / 2) : ℝ) * (1) * ((1 + ((-1) * a)))^2 + (1 : ℝ) * (1) * ((1 + ((-1) * a * b)))^2 + ((2005 / 2) : ℝ) * (1) * ((1 + ((-1) * b)))^2 + ((2007 / 2) : ℝ) * (1) * ((a + ((-1) * b)))^2 + (2005 : ℝ) * (b) * ((a + ((-1) * b)))^2 + ((2005 / 2) : ℝ) * (a) * ((1 + ((-1) * a)))^2 + ((6015 / 2) : ℝ) * (a) * ((1 + ((-1) * b)))^2 + ((2005 / 2) : ℝ) * (a) * ((a + ((-1) * b)))^2 := by positivity
      _ = ((a^2 + 2005*b + 2006)*(b^2 + 2005*a + 2006)) - ((2007*a + 2005)*(2007*b + 2005)) := by ring
  exact sub_nonneg.mp h
