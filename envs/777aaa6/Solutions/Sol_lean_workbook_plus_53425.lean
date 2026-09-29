-- Prove2me | solution 1 for lean_workbook_plus_53425
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:01.686746+00:00
-- url     : https://prove2.me/submissions/e605a244-855b-448c-8147-778afc560e3e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x^2 - x + 1 / 4 ≥ 0 := by
  intros
  have h : (0 : ℝ) ≤ (x^2 - x + 1 / 4) - (0) := by
    calc
      0 ≤ ((1 / 4) : ℝ) * ((1 + ((-2) * x)))^2 := by positivity
      _ = (x^2 - x + 1 / 4) - (0) := by ring
  exact sub_nonneg.mp h
