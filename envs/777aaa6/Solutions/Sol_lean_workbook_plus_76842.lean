-- Prove2me | solution 1 for lean_workbook_plus_76842
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:34.92615+00:00
-- url     : https://prove2.me/submissions/ff36fb85-8d0d-414d-b745-2fd70a6444c2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution : ∀ x : ℝ, x^4 - x^3 + x^2 - x + 1 > 0 := by
  intro x
  nlinarith only [sq_nonneg (x^2 - x/2), sq_nonneg (x - (2/3 : ℝ))]
