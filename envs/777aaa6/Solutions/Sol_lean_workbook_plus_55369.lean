-- Prove2me | solution 1 for lean_workbook_plus_55369
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:34:34.263411+00:00
-- url     : https://prove2.me/submissions/aa6f3ffb-525a-4f4e-b0d3-15cd5ede915c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) :
    x 1 + 4 * x 2 + 9 * x 3 + 16 * x 4 + 25 * x 5 + 36 * x 6 + 49 * x 7 = 1 ∧
    4 * x 1 + 9 * x 2 + 16 * x 3 + 25 * x 4 + 36 * x 5 + 49 * x 6 + 64 * x 7 = 12 ∧
    9 * x 1 + 16 * x 2 + 25 * x 3 + 36 * x 4 + 49 * x 5 + 64 * x 6 + 81 * x 7 = 123 →
    16 * x 1 + 25 * x 2 + 36 * x 3 + 49 * x 4 + 64 * x 5 + 81 * x 6 + 100 * x 7 = 334 := by
  rintro ⟨h₁, h₂, h₃⟩
  linear_combination h₁ - 3 * h₂ + 3 * h₃

#print axioms solution
