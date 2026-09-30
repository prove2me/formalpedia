-- Prove2me | solution 1 for lean_workbook_plus_71999
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:55:28.659355+00:00
-- url     : https://prove2.me/submissions/3f7399f8-1d6e-4a59-aa3e-44ac07f7ee3d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) :
    (a^2+1)*(b^2+1)*(c^2+1) ≥ (a*b+1)*(b*c+1)*(c*a+1) := by
  have hab := mul_nonneg (sq_nonneg (a-b)) (add_nonneg (sq_nonneg c) zero_le_one)
  have hbc := mul_nonneg (sq_nonneg (b-c)) (add_nonneg (sq_nonneg a) zero_le_one)
  have hca := mul_nonneg (sq_nonneg (c-a)) (add_nonneg (sq_nonneg b) zero_le_one)
  nlinarith only [hab, hbc, hca]
