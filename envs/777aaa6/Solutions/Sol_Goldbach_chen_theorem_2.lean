-- Prove2me | solution 2 for Goldbach.chen_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:49:07.523802+00:00
-- url     : https://prove2.me/submissions/666ba3d0-9f80-4b08-82dc-3279968afc7d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Goldbach_chen_theorem_sieve
set_option autoImplicit false

theorem solution :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧ n = p + q := by
  exact Goldbach.chen_theorem_sieve

#print axioms solution
