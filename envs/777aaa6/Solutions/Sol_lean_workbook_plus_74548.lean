-- Prove2me | solution 1 for lean_workbook_plus_74548
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:39:21.840752+00:00
-- url     : https://prove2.me/submissions/37893c4e-b5fc-4600-a95e-8153ded0b2c4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y : ℝ) : x^2 + y^2 ≥ x*y + x + y - 1 := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (x-1), sq_nonneg (y-1)]
