-- Prove2me | solution 1 for lean_workbook_plus_29636
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:40:28.234603+00:00
-- url     : https://prove2.me/submissions/33a394e6-1930-4e8c-9b4b-7b05a38a39ad

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℤ) (h : a + b + c ≠ 0) (habc : a + b + c ∣ a^2 + b^2 + c^2) : ∃ n : ℕ, a + b + c ∣ a^n + b^n + c^n :=
  ⟨1, by simp⟩
