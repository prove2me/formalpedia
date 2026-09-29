-- Prove2me | solution 1 for lean_workbook_plus_16752
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:17:51.431825+00:00
-- url     : https://prove2.me/submissions/279bbb0f-2860-4565-a6e7-247514e214c0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z ε : ℝ) (h : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) < ε) :
  |x| < ε ∧ |y| < ε ∧ |z| < ε := by
  have bound (t : ℝ) (ht : t^2 ≤ x^2+y^2+z^2) : |t| < ε := by
    calc
      |t| = Real.sqrt (t^2) := (Real.sqrt_sq_eq_abs t).symm
      _ ≤ Real.sqrt (x^2+y^2+z^2) := Real.sqrt_le_sqrt ht
      _ < ε := h
  exact ⟨bound x (by nlinarith [sq_nonneg y, sq_nonneg z]), bound y (by nlinarith [sq_nonneg x, sq_nonneg z]), bound z (by nlinarith [sq_nonneg x, sq_nonneg y])⟩
