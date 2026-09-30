-- Prove2me | solution 1 for lean_workbook_plus_17534
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:08:23.105178+00:00
-- url     : https://prove2.me/submissions/6f275781-6972-441d-8447-84f7ad6b7143

import Mathlib
set_option autoImplicit false

theorem solution  (b c : ℝ)
  (h₀ : 2 * b - 1 / c > 1) :
  2 * b > 1 + 1 / c ∧ b > 1 / 2 + 1 / (2 * c) ∧ b + 1 > 3 / 2 + 1 / (2 * c)   := by
  have hdiv : (1 : ℝ) / (2 * c) = (1 / c) / 2 := by
    rw [div_div, mul_comm c (2 : ℝ)]
  refine ⟨?_, ?_, ?_⟩
  · linarith only [h₀]
  · rw [hdiv]
    linarith only [h₀]
  · rw [hdiv]
    linarith only [h₀]

#print axioms solution
