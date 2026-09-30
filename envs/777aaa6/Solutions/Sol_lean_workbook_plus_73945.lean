-- Prove2me | solution 1 for lean_workbook_plus_73945
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:25:27.746975+00:00
-- url     : https://prove2.me/submissions/61ef4c2e-2c36-4666-b9f5-1d4af381f8fa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x : ℝ) : (x + 1) * (x + 2) * (x + 3) * (x + 4) ≥ -1 := by
  nlinarith [sq_nonneg (x ^ 2 + 5 * x + 5)]

#print axioms solution
