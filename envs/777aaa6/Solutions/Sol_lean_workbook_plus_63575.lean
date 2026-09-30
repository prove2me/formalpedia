-- Prove2me | solution 1 for lean_workbook_plus_63575
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:03:12.683403+00:00
-- url     : https://prove2.me/submissions/733f10b2-8dc1-4113-a133-66411d0e6621

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem solution (a b c d : ℝ) :
    (a*b*c+a*c*d+a*b*d+b*c*d-a-b-c-d)^2 +
      (a*b*c*d-a*b-a*c-a*d-b*c-b*d-c*d+1)^2 ≥ 1 := by
  have ha : 1 ≤ a^2+1 := by nlinarith only [sq_nonneg a]
  have hb : 1 ≤ b^2+1 := by nlinarith only [sq_nonneg b]
  have hc : 1 ≤ c^2+1 := by nlinarith only [sq_nonneg c]
  have hd : 1 ≤ d^2+1 := by nlinarith only [sq_nonneg d]
  calc
    (a*b*c+a*c*d+a*b*d+b*c*d-a-b-c-d)^2 +
        (a*b*c*d-a*b-a*c-a*d-b*c-b*d-c*d+1)^2 =
        (a^2+1)*(b^2+1)*(c^2+1)*(d^2+1) := by ring
    _ ≥ 1 := one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ha hb) hc) hd
