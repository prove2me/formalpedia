-- Prove2me | solution 1 for lean_workbook_plus_56494
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:13:45.25985+00:00
-- url     : https://prove2.me/submissions/26fcc6bc-a6ed-4f98-a3aa-6c29abd086f2

import Mathlib
set_option autoImplicit false

theorem solution : ∀ n : ℤ, 2 ∣ (n^5 - n)   := by
  intro n
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ := Int.even_or_odd n
  all_goals ring_nf; simp [Int.dvd_iff_emod_eq_zero, Int.add_emod, Int.mul_emod]

#print axioms solution
