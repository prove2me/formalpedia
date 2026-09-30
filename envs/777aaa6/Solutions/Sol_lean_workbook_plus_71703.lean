-- Prove2me | solution 1 for lean_workbook_plus_71703
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:53:58.786753+00:00
-- url     : https://prove2.me/submissions/b353f522-cff9-40e8-b8d6-b66ace47e350

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : x ≠ 0) :
    Real.sqrt ((y ^ 2 + z ^ 2) / x ^ 2) ≤ (1 + (y ^ 2 + z ^ 2) / x ^ 2) / 2 := by
  have ht : 0 ≤ (y ^ 2 + z ^ 2) / x ^ 2 := by positivity
  have hs := Real.sq_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt ((y ^ 2 + z ^ 2) / x ^ 2) - 1)]

#print axioms solution
