-- Prove2me | solution 1 for lean_workbook_plus_78744
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:54:17.872184+00:00
-- url     : https://prove2.me/submissions/9fc1bb3e-1cca-458f-bacb-4b3bac6bb1b6

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ)
    (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c ≥ 3) :
    a^4 + b^3 + c^2 ≥ a^3 + b^2 + c := by
  have hpa : 0 ≤ a^2 + a + 1 := by nlinarith [sq_nonneg a, ha.1]
  have hpb : 0 ≤ b + 1 := by linarith only [ha.2.1]
  have hqa := mul_nonneg (sq_nonneg (a-1)) hpa
  have hqb := mul_nonneg (sq_nonneg (b-1)) hpb
  nlinarith only [hqa, hqb, sq_nonneg (c-1), ha.2.2.2]
