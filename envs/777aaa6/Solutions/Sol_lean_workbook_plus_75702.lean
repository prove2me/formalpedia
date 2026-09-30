-- Prove2me | solution 1 for lean_workbook_plus_75702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T18:06:03.364982+00:00
-- url     : https://prove2.me/submissions/10559e84-7870-455d-b09d-45db758d0fa9

import Mathlib
set_option autoImplicit false

theorem solution {p : ℕ} (hp : p.Prime) {a : ℤ} {n : ℕ} : (∃ y, y^2 ≡ a [ZMOD p^n]) ↔ (∃ y, y^2 - a ≡ 0 [ZMOD p^n])   := by
  simp [Int.modEq_iff_dvd, sub_eq_zero]

#print axioms solution
