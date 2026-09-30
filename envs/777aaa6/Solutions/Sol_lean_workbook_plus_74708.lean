-- Prove2me | solution 1 for lean_workbook_plus_74708
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:06:00.600228+00:00
-- url     : https://prove2.me/submissions/7ab594a6-bedd-48d1-bfca-dbf2246c7148

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) + f (x - y) = 2 * (f x + f y)) : f 0 = 0   := by
  have h1 := hf 0 0
  simp at h1
  linarith

#print axioms solution
