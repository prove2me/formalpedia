-- Prove2me | solution 1 for lean_workbook_plus_29698
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:04.159246+00:00
-- url     : https://prove2.me/submissions/31fd7ca7-769d-444a-b86b-d8343408da46

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y p q : ℝ) (hp : p = x - 1) (hq : q = 1 - y) : p^2 + q^2 + 1 ≥ p * q + p + q := by
  intros
  have h : (0 : ℝ) ≤ (p^2 + q^2 + 1) - (p * q + p + q) := by
    calc
      0 ≤ ((1 / 2) : ℝ) * ((1 + ((-1) * q)))^2 + ((1 / 2) : ℝ) * ((1 + ((-1) * p)))^2 + ((1 / 2) : ℝ) * ((q + ((-1) * p)))^2 := by positivity
      _ = (p^2 + q^2 + 1) - (p * q + p + q) := by ring
  exact sub_nonneg.mp h
