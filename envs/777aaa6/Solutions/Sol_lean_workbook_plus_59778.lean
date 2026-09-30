-- Prove2me | solution 1 for lean_workbook_plus_59778
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:34:33.393803+00:00
-- url     : https://prove2.me/submissions/95f045cc-9285-4988-9408-c3f214fbab2a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a : ℝ) : a ^ 2 - a + 1 ≥ Real.sqrt ((a ^ 4 + 1) / 2) := by
  apply (Real.sqrt_le_left (by nlinarith [sq_nonneg (a - 1 / 2)])).mpr
  nlinarith [sq_nonneg ((a - 1) ^ 2)]

#print axioms solution
