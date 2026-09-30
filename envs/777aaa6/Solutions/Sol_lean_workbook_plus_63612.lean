-- Prove2me | solution 1 for lean_workbook_plus_63612
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:10:21.886962+00:00
-- url     : https://prove2.me/submissions/cb96f673-e7b6-4864-86a1-ccb1207ae5ea

import Mathlib
set_option autoImplicit false

theorem solution (x : ℝ) : 2 - Real.sqrt 3 = 1 / 2 * (Real.sqrt 3 - 1) ^ 2   := by
  ring_nf
  rw [Real.sq_sqrt] <;> linarith

#print axioms solution
