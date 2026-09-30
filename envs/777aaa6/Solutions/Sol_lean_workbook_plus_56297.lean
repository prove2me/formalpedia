-- Prove2me | solution 1 for lean_workbook_plus_56297
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:44.355724+00:00
-- url     : https://prove2.me/submissions/84acbc60-6430-4c11-a3fd-40e6cb863766

import Mathlib
set_option autoImplicit false

theorem solution (n : ℤ) (h : n%2 = 1) : ∃ k : ℤ, n = 4*k + 1 ∨ n = 4*k + 3   := by
  refine ⟨n / 4, ?_⟩
  omega

#print axioms solution
