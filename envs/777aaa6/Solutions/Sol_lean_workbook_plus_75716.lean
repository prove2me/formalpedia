-- Prove2me | solution 1 for lean_workbook_plus_75716
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:28:01.318688+00:00
-- url     : https://prove2.me/submissions/d2664f8e-3925-442e-ad09-cbc04936fc0b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (b c : ℝ) : |b - c| = Real.sqrt (2 * (b ^ 2 + c ^ 2) - (b + c) ^ 2) := by
  have he : 2 * (b ^ 2 + c ^ 2) - (b + c) ^ 2 = (b - c) ^ 2 := by ring
  rw [he, Real.sqrt_sq_eq_abs]

#print axioms solution
