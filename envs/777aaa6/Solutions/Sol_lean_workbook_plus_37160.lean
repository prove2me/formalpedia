-- Prove2me | solution 1 for lean_workbook_plus_37160
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:23.834678+00:00
-- url     : https://prove2.me/submissions/2ae1a6d6-dcc0-4b10-92bf-7572a1685554

import Mathlib

set_option autoImplicit false

theorem small_prime_exceptions :
    (Nat.choose (2 * 2) 2) % (2 ^ 3) = 6 ∧
    (Nat.choose (2 * 3) 3) % (3 ^ 3) = 20 := by decide

theorem solution : ¬ (∀ p : ℕ, p.Prime → (Nat.choose (2 * p) p) % (p ^ 3) = 2) := by
  intro h
  have h2 := h 2 (by decide)
  have h6 := small_prime_exceptions.1
  omega

#print axioms solution
