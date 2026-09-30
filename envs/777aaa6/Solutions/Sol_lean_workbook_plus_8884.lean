-- Prove2me | solution 1 for lean_workbook_plus_8884
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:22:22.671785+00:00
-- url     : https://prove2.me/submissions/e0628bff-8cbd-41cb-929b-df82a7da9e32

import Mathlib

theorem five_variable_identity {R : Type*} [CommRing R] (a b c d e : R) :
    (a*b+b*c+c*d+d*e+e*a)*(a*c+b*d+e*c+a*d+b*e) -
      5*d*e*c*a - 5*d*e*a*b - 5*c*b*d*e - 5*e*b*c*a - 5*a*b*c*d =
      c*e*(a-b)^2 + d*e*(a-c)^2 + b*c*(a-d)^2 + b*d*(a-e)^2 +
      a*d*(b-c)^2 + a*e*(b-d)^2 + c*d*(b-e)^2 + b*e*(c-d)^2 +
      a*b*(c-e)^2 + a*c*(d-e)^2 := by ring

theorem nonnegative_remainder (a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    0 ≤ (a*b+b*c+c*d+d*e+e*a)*(a*c+b*d+e*c+a*d+b*e) -
      5*d*e*c*a - 5*d*e*a*b - 5*c*b*d*e - 5*e*b*c*a - 5*a*b*c*d := by
  rw [five_variable_identity]
  positivity

theorem solution (a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) :
    (a*b+b*c+c*d+d*e+e*a)*(a*c+b*d+e*c+a*d+b*e) -
      5*d*e*c*a - 5*d*e*a*b - 5*c*b*d*e - 5*e*b*c*a - 5*a*b*c*d =
      c*e*(a-b)^2 + d*e*(a-c)^2 + b*c*(a-d)^2 + b*d*(a-e)^2 +
      a*d*(b-c)^2 + a*e*(b-d)^2 + c*d*(b-e)^2 + b*e*(c-d)^2 +
      a*b*(c-e)^2 + a*c*(d-e)^2 :=
  five_variable_identity a b c d e
