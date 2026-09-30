-- Prove2me | solution 1 for lean_workbook_plus_55695
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:44:47.509252+00:00
-- url     : https://prove2.me/submissions/db6b7430-af3e-40c2-a2d5-67b7ee2ac628

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b) :
    Real.sqrt a + Real.sqrt b ≤ Real.sqrt (2 * (a + b)) := by
  apply Real.le_sqrt_of_sq_le
  nlinarith [Real.sq_sqrt hab.1, Real.sq_sqrt hab.2,
    sq_nonneg (Real.sqrt a - Real.sqrt b)]

#print axioms solution
