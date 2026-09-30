-- Prove2me | solution 1 for lean_workbook_plus_64078
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:03:00.964646+00:00
-- url     : https://prove2.me/submissions/cffa8010-85da-4481-9e09-d8936fbbe34b

import Mathlib
set_option autoImplicit false

theorem solution (p : ℕ) (hp : p.Prime) : ∃ q : ℕ, q.Prime ∧ q ≡ 5 [ZMOD 8]   := by
  use 5
  exact ⟨Nat.prime_five, by decide⟩

#print axioms solution
