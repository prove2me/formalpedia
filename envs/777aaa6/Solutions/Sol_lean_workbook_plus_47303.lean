-- Prove2me | solution 1 for lean_workbook_plus_47303
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:11:29.718811+00:00
-- url     : https://prove2.me/submissions/3a3e69d4-6125-4dc1-aff4-72e564b9d074

import Mathlib.Analysis.Complex.Basic

theorem solution (a₁ a₂ b : ℤ)
  (h₀ : a₁ ≡ a₂ [ZMOD 6])
  (h₁ : b ≡ b [ZMOD 6]) :
  6 * a₁ * b ≡ 6 * a₂ * b [ZMOD 6] :=
  (h₀.mul_left 6).mul_right b
