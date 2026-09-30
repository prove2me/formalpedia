-- Prove2me | solution 1 for lean_workbook_plus_80559
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:49.705275+00:00
-- url     : https://prove2.me/submissions/d1114844-9567-4c95-ae33-67213819fd7d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 < x) (h : x * (x ^ 4 - x ^ 2 + 1) ≥ 3) :
    x ^ 6 ≥ 5 := by
  have hprod : 0 ≤ (x^2 + 1) * (x * (x^4 - x^2 + 1) - 3) :=
    mul_nonneg (by positivity) (by linarith)
  have hkey : 0 ≤ x * (x^6 - 5) := by
    nlinarith [sq_nonneg (x - 1)]
  by_contra hnot
  have hneg : x * (x^6 - 5) < 0 := mul_neg_of_pos_of_neg hx (by linarith)
  linarith
