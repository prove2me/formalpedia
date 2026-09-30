-- Prove2me | solution 1 for lean_workbook_plus_10658
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:14:40.194719+00:00
-- url     : https://prove2.me/submissions/0cefdf47-4996-4882-89fa-a6b06293f371

import Mathlib.Analysis.Complex.Basic

theorem solution (x u v : ℤ) (h₁ : x^2 - 1 = 3 * u^2) (h₂ : x^2 + 1 = v^2) : ∃ x u v : ℤ, x^2 - 1 = 3 * u^2 ∧ x^2 + 1 = v^2 :=
  ⟨x, u, v, h₁, h₂⟩
