-- Prove2me | solution 1 for lean_workbook_plus_78642
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:38:15.361453+00:00
-- url     : https://prove2.me/submissions/9f5558b9-0ef5-4a91-b00a-eaba29fddc71

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) (hx : x ≥ 0) : 8 * x ^ 4 + 10 * x ^ 3 - 21 * x ^ 2 + 27 ≥ 0 := by
  have hc := mul_nonneg hx (sq_nonneg x)
  nlinarith [sq_nonneg (16 * x ^ 2 - 21)]

#print axioms solution
