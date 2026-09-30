-- Prove2me | solution 2 for goldbach_odd_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:38:06.811645+00:00
-- url     : https://prove2.me/submissions/554f1ed0-5672-4464-918e-907cfd6548e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

theorem solution :
    ∀ n : ℕ, 7 < n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r := by
  intro n hn hndvd
  have hodd : Odd n :=
    Nat.not_even_iff_odd.mp (fun he => hndvd (even_iff_two_dvd.mp he))
  have ⟨k, hk⟩ := hodd
  by_cases hbig : 10 ^ 27 ≤ n
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.three_odd_primes_ge_10pow27 n hbig hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.verified_three_odd_primes_to_8875e30 n
        (by omega) (by omega) hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
