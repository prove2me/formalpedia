-- Prove2me | solution 1 for lean_workbook_plus_53901
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:39:36.388011+00:00
-- url     : https://prove2.me/submissions/a979accf-7fff-451e-a95e-771d1e854579

import Mathlib.Analysis.Complex.Basic

theorem solution  (x : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (3 / 4) * (x - 1)^2)
  (h₁ : x = 5) :
  f x = 12 := by
  rw [h₀, h₁]; norm_num
