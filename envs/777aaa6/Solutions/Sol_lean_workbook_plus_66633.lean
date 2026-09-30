-- Prove2me | solution 1 for lean_workbook_plus_66633
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T16:45:37.554674+00:00
-- url     : https://prove2.me/submissions/302ed122-dc38-46fa-820c-397c67722c7a

import Mathlib
set_option autoImplicit false

theorem solution : ∀ a b c : ℝ, c^4 + c^4 + a^4 + b^4 ≥ 4 * a * b * c^2   := by
  intro a b c
  nlinarith [sq_nonneg (c^2 - a * b), sq_nonneg (a^2 - b^2), sq_nonneg (b^2 - c^2)]

#print axioms solution
