-- Prove2me | solution 1 for lean_workbook_plus_73111
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:16:50.574071+00:00
-- url     : https://prove2.me/submissions/c74fd64b-a7e8-4658-bde9-8331eac8d14e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (h1 : a > 0 ∧ b > 0 ∧ c > 0)
    (h2 : a * (b + c) = b * c) : a / (b + c) ≤ 1 / 4 := by
  have hden : 0 < b + c := add_pos h1.2.1 h1.2.2
  apply (div_le_iff₀ hden).mpr
  nlinarith [sq_nonneg (b - c)]

#print axioms solution
