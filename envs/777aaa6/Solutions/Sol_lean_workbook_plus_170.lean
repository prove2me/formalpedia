-- Prove2me | solution 1 for lean_workbook_plus_170
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:36:53.674079+00:00
-- url     : https://prove2.me/submissions/4f270008-5797-43a2-a21e-07c8f90e448d

import Mathlib

theorem solution {a b c s : ℝ} (hs : s = (a + b + c) / 2) :
    (a * b + b * c + c * a) / 4 ≥
      (s - b) * (s - c) + (s - a) * (s - b) + (s - c) * (s - a) := by
  subst s
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
