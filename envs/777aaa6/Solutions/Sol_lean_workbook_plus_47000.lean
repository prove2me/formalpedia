-- Prove2me | solution 1 for lean_workbook_plus_47000
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:45:00.764849+00:00
-- url     : https://prove2.me/submissions/8e277aa4-0c93-4091-a908-536a1dad2bd6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem remainder_identity (a b c : ℝ) :
    a^3*b^4+b^3*c^4+c^3*a^4-
      (2*a*b*c*(a*b+b*c+c*a)^2-5*(a*b*c)^2*(a+b+c)) =
      a^3*b^2*(b-c)^2+b^3*c^2*(c-a)^2+c^3*a^2*(a-b)^2 := by
  ring

theorem nonnegative_bound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    2*a*b*c*(a*b+b*c+c*a)^2-5*(a*b*c)^2*(a+b+c) ≤
      a^3*b^4+b^3*c^4+c^3*a^4 := by
  apply sub_nonneg.mp
  rw [remainder_identity]
  positivity

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^3*b^4+b^3*c^4+c^3*a^4 >=
      2*a*b*c*(a*b+b*c+c*a)^2-5*(a*b*c)^2*(a+b+c) :=
  nonnegative_bound a b c (le_of_lt ha) (le_of_lt hb) (le_of_lt hc)
