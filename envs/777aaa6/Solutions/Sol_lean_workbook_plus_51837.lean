-- Prove2me | solution 1 for lean_workbook_plus_51837
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:47.295278+00:00
-- url     : https://prove2.me/submissions/a74e0917-2305-4837-8f12-617680e0d3b3

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) (p q : ℝ) (hx : x ^ 3 + p * x + q = 0) :
    4 * x * q ≤ p ^ 2 := by
  have hm := congrArg (fun t : ℝ => 4 * x * t) hx
  nlinarith [sq_nonneg (p + 2 * x ^ 2)]

#print axioms solution
