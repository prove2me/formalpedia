-- Prove2me | solution 1 for lean_workbook_plus_13042
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:33.504104+00:00
-- url     : https://prove2.me/submissions/d8ffa213-e901-488a-9b6f-ef7b37320d29

import Mathlib
set_option autoImplicit false

theorem solution : ∀ x y : ℤ, x ≡ 1 [ZMOD 3] ∧ y ≡ 2 [ZMOD 3] → ¬ 3 ∣ (x * y)   := by
  simp (config := { contextual := true }) [Int.ModEq, Int.dvd_iff_emod_eq_zero, Int.mul_emod]

#print axioms solution
