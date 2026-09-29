-- Prove2me | solution 1 for lean_workbook_plus_75350
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:57:30.332832+00:00
-- url     : https://prove2.me/submissions/94994668-4612-48d3-b27f-88a5fb2905c4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private theorem source_sum_two_squares (n : ℤ) :
    (∃ a b : ℤ, a ^ 2 + b ^ 2 = n) → ∃ c d : ℤ, c ^ 2 + d ^ 2 = 2 * n := by
  rintro ⟨a, b, h⟩
  refine ⟨a + b, a - b, ?_⟩
  nlinarith only [h]

theorem solution (n : ℤ) : ∃ a b : ℤ, a ^ 2 + b ^ 2 = n → ∃ c d : ℤ, c ^ 2 + d ^ 2 = 2 * n := by
  exact ⟨0, 0, fun h => source_sum_two_squares n ⟨0, 0, h⟩⟩
