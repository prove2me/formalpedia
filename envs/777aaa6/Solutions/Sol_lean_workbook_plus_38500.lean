-- Prove2me | solution 1 for lean_workbook_plus_38500
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:02.604499+00:00
-- url     : https://prove2.me/submissions/215ce5f6-900e-439a-bb1c-49aa18471fb4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b t : ℚ) (h₁ : a^5 + b^5 = 2 * a^2 * b^2) (h₂ : 1 - a * b = t^2) : t ∈ Set.univ := by
  norm_num
