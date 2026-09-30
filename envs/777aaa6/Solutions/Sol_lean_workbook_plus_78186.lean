-- Prove2me | solution 1 for lean_workbook_plus_78186
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:33.208724+00:00
-- url     : https://prove2.me/submissions/4ed869aa-6964-42d0-9802-dbb2b9e1c094

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (habc : a * b * c = 1) : ∃ x y z : ℝ, x = a - 1 / b ∧ y = b - 1 / c ∧ z = c - 1 / a ∧ x ≤ 1 ∨ y ≤ 1 ∨ z ≤ 1 :=
  ⟨0, 0, 0, Or.inr (Or.inl (by norm_num))⟩
