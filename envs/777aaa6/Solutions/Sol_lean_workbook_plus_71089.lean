-- Prove2me | solution 1 for lean_workbook_plus_71089
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:55:27.828657+00:00
-- url     : https://prove2.me/submissions/b76b1c1d-ab7e-45cd-8231-615d03846239

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (h : a + b + c = 3) :
    a^3 + b^3 + c^3 - 3*a*b*c ≥ (9/4)*(a^2+b^2-2*a*b) := by
  have hm := congrArg (fun t : ℝ => t*(a^2+b^2+c^2-a*b-b*c-c*a)) h
  nlinarith only [hm, sq_nonneg (a+b-2*c)]
