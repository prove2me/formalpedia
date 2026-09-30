-- Prove2me | solution 1 for lean_workbook_plus_69533
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:44:33.754173+00:00
-- url     : https://prove2.me/submissions/61dd908f-4be3-4ece-95a4-17ce4cf36ceb

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem mixed_remainder_identity (a b c : ℝ) :
    a^4+b^4+c^4+a^2*b^2+a^2*c^2+b^2*c^2-
      (a^3*b+b^3*a+a^3*c+c^3*a+b^3*c+c^3*b) =
      (((a-b)*(a+b-c))^2+((b-c)*(b+c-a))^2+((c-a)*(c+a-b))^2+
        (a*b-b*c)^2+(b*c-c*a)^2+(c*a-a*b)^2)/2 := by
  ring

theorem general_bound (a b c : ℝ) :
    a^3*b+b^3*a+a^3*c+c^3*a+b^3*c+c^3*b ≤
      a^4+b^4+c^4+a^2*b^2+a^2*c^2+b^2*c^2 := by
  nlinarith only [sq_nonneg ((a-b)*(a+b-c)), sq_nonneg ((b-c)*(b+c-a)),
    sq_nonneg ((c-a)*(c+a-b)), sq_nonneg (a*b-b*c), sq_nonneg (b*c-c*a),
    sq_nonneg (c*a-a*b)]

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a^4+b^4+c^4+a^2*b^2+a^2*c^2+b^2*c^2 ≥
      a^3*b+b^3*a+a^3*c+c^3*a+b^3*c+c^3*b := general_bound a b c
