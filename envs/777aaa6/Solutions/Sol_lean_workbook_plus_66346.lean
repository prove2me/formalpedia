-- Prove2me | solution 1 for lean_workbook_plus_66346
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:10.643677+00:00
-- url     : https://prove2.me/submissions/6428e4c8-0c88-4216-9716-c3c77621b8da

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (h : n > 0) : Even (2 ^ n)   := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
  simp [pow_succ]

#print axioms solution
