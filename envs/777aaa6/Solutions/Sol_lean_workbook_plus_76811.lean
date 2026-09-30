-- Prove2me | solution 1 for lean_workbook_plus_76811
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:49:06.988683+00:00
-- url     : https://prove2.me/submissions/280a881e-18fa-4429-98c0-2d88900853d0

import Mathlib
set_option autoImplicit false

theorem solution (k : ℤ) : (∃ n : ℤ, k = 13*n + 4) ↔ (k ≡ 4 [ZMOD 13])   := by
  simp only [Int.ModEq]
  constructor
  intro h
  obtain ⟨n, rfl⟩ := h
  simp [Int.add_emod, Int.mul_emod, Int.emod_emod]
  intro h
  use (k - 4)/13
  omega

#print axioms solution
