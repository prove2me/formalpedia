-- Prove2me | solution 1 for lean_workbook_plus_12630
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:48.368987+00:00
-- url     : https://prove2.me/submissions/257fbfc7-4e66-4474-af17-5051f94ded27

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : c^2 = a^2 + b^2) :
  (b * (b + c)) / (a * (a + c)) = (2 * b * (b + c - a) + 2 * a * b) / (2 * a * (a + c - b) + 2 * a * b) := by
  (intros; field_simp; ring)
