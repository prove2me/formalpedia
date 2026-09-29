-- Prove2me | solution 1 for lean_workbook_plus_16580
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:14.841968+00:00
-- url     : https://prove2.me/submissions/882aad25-3407-4ba2-9e98-345b30887a73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y a : ℝ) (h₁ : x = (a^3 + a) / (a^3 + 1)) (h₂ : y = (a^2 + 1) / (a^3 + 1)) : x = (a^3 + a) / (a^3 + 1) ∧ y = (a^2 + 1) / (a^3 + 1) := by
  (intros; simp_all)
