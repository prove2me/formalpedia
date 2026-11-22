-- Prove2me | solution 1 for Erdos390.dvd_of_bounded_prime_factors
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-06T05:24:07.091829+00:00
-- url     : https://prove2.me/submissions/ae8a6424-c472-4c69-83bc-a30128c650cd

import Mathlib

theorem solution
    {D P B : ℕ} (hD : D ≠ 0) (hP : P ≠ 0)
    (hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ D → ℓ ≤ B)
    (hval : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≤ B → D.factorization ℓ ≤ P.factorization ℓ) :
    D ∣ P := by
  rw [← Nat.factorization_le_iff_dvd hD hP]
  intro ℓ
  by_cases hℓ : ℓ.Prime
  · by_cases hdvd : ℓ ∣ D
    · exact hval ℓ hℓ (hprime ℓ hℓ hdvd)
    · rw [Nat.factorization_eq_zero_of_not_dvd hdvd]
      exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime _ hℓ]
    exact Nat.zero_le _
