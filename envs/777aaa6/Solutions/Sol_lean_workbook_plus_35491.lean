-- Prove2me | solution 1 for lean_workbook_plus_35491
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:40:58.616285+00:00
-- url     : https://prove2.me/submissions/f3403d2d-1042-4b9d-812f-2222fb7ec5f1

import Mathlib.Analysis.Complex.Basic

theorem solution  (a b c : ℝ)
  (x y z : ℝ)
  (h₀ : x = a / b)
  (h₁ : y = b / c)
  (h₂ : z = c / a) :
  a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
