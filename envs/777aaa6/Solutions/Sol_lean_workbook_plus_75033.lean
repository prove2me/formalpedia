-- Prove2me | solution 1 for lean_workbook_plus_75033
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:13.744302+00:00
-- url     : https://prove2.me/submissions/950d2b91-723f-4191-970d-4e03f9842e04

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : 4 * y - x ≤ 12) (h2 : y + 4 * x ≤ 20) : 9 - x ^ 2 - y ^ 2 + x * y + 2 * (x + y) ≤ 13 := by
  intros
  have h : (0 : ℝ) ≤ (13) - (9 - x ^ 2 - y ^ 2 + x * y + 2 * (x + y)) := by
    calc
      0 ≤ (2 : ℝ) * ((1 + ((-1 / 2) * y)))^2 + (2 : ℝ) * ((1 + ((-1 / 2) * x)))^2 + ((1 / 2) : ℝ) * ((y + ((-1) * x)))^2 := by positivity
      _ = (13) - (9 - x ^ 2 - y ^ 2 + x * y + 2 * (x + y)) := by ring
  exact sub_nonneg.mp h
