-- Prove2me | solution 1 for lean_workbook_plus_2509
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:53.095537+00:00
-- url     : https://prove2.me/submissions/0f9647b1-d26f-4e66-ad81-f4a7cd72ad01

import Mathlib

theorem solution {a b c : ℝ} (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    12 * (a ^ 4 + b ^ 4 + c ^ 4) ≥
      12 * (b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - a ^ 2 * b ^ 2) := by
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - c ^ 2), sq_nonneg (a ^ 2),
    sq_nonneg (b ^ 2), sq_nonneg (c ^ 2)]
