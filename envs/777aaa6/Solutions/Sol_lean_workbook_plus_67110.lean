-- Prove2me | solution 1 for lean_workbook_plus_67110
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:59:16.195141+00:00
-- url     : https://prove2.me/submissions/adf4488b-f1fd-47ac-80bb-e808fc87557b

import Mathlib
set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (h₁ : ∀ x y, g (x*y) = g x * g y) (h₂ : g 2 = 4) : g 4 = 16 ∧ g 16 = 256   := by
  have h4 : g 4 = 16 := by
    calc
      g 4 = g (2 * 2) := by norm_num
      _ = g 2 * g 2 := h₁ 2 2
      _ = 16 := by norm_num [h₂]
  constructor
  · exact h4
  · calc
      g 16 = g (4 * 4) := by norm_num
      _ = g 4 * g 4 := h₁ 4 4
      _ = 256 := by norm_num [h4]

#print axioms solution
