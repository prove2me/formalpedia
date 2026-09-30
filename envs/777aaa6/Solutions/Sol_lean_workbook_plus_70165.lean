-- Prove2me | solution 1 for lean_workbook_plus_70165
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:31.292223+00:00
-- url     : https://prove2.me/submissions/25d916c6-2617-4755-93d8-29a5a9e01212

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f x + f y)
    (h : f 1 = 3) : f 2 = 6 := by
  have h2 := hf 1 1
  norm_num [h] at h2
  exact h2

#print axioms solution
