-- Prove2me | solution 1 for lean_workbook_plus_34130
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:35:54.448219+00:00
-- url     : https://prove2.me/submissions/1fe0aafe-80a0-40d3-8024-d0d2cd566d60

import Mathlib
set_option autoImplicit false

theorem solution (V : Type*) (K : Type*) [Field K] [AddCommGroup V] [Module K V] (u : V) : u + u = 2 • u   := by
  simp [two_smul]

#print axioms solution
