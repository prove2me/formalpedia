-- Prove2me | solution 1 for lean_workbook_plus_50741
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:16:51.907514+00:00
-- url     : https://prove2.me/submissions/4fa16fd1-6885-4ff1-87ad-253088df0c82

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y : ℝ, x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 → x < y → (1 / (2 - x)) < (1 / (2 - y))   := by
  rintro x y ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩ hxy
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

#print axioms solution
