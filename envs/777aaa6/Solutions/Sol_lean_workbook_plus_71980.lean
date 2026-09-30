-- Prove2me | solution 1 for lean_workbook_plus_71980
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:06:17.685291+00:00
-- url     : https://prove2.me/submissions/94d4f04f-8687-4369-92d3-9d3c705e9445

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private lemma weighted_pair (a b : ℝ) :
    42 * a ^ 3 * b ^ 3 ≤ a ^ 6 + 11 * b ^ 6 + 30 * a ^ 4 * b ^ 2 := by
  nlinarith only [sq_nonneg ((a-b)*a*(a+b)),
    sq_nonneg ((a-b)*b*(32*a+11*b)), sq_nonneg ((a-b)*b^2)]

theorem solution (a b c : ℝ) :
    2 * (a ^ 6 + b ^ 6 + c ^ 6) + 5 * (a ^ 4 * b ^ 2 + b ^ 4 * c ^ 2 + c ^ 4 * a ^ 2) ≥
      7 * (a ^ 3 * b ^ 3 + b ^ 3 * c ^ 3 + c ^ 3 * a ^ 3) := by
  nlinarith only [weighted_pair a b, weighted_pair b c, weighted_pair c a]

#print axioms solution
