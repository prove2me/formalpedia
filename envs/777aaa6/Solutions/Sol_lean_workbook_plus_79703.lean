-- Prove2me | solution 1 for lean_workbook_plus_79703
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:07.878744+00:00
-- url     : https://prove2.me/submissions/af2a9a36-9147-4ef9-8bd1-f83c1dbd3434

import Mathlib
set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : f = fun x => x^2) :
    ∀ x y, f (f x + y) = f (x^2-y) + 4*y*f x := by
  subst f
  intro x y
  dsimp
  ring

#print axioms solution
