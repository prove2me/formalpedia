-- Prove2me | solution 1 for odd_goldbach_variant
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:38:06.103282+00:00
-- url     : https://prove2.me/submissions/9b4ff591-48ac-42da-aaff-583c12ee50df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_three_odd_primes_to_8875e30
import Theorems.Thm_WeakGoldbach_three_odd_primes_ge_10pow27

theorem solution :
    ∀ n : ℕ, 7 ≤ n → ¬ 2 ∣ n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      n = p + q + r ∧ p ≤ q ∧ q ≤ r := by
  intro n hn hndvd
  have hodd : Odd n :=
    Nat.not_even_iff_odd.mp (fun he => hndvd (even_iff_two_dvd.mp he))
  have ⟨k, hk⟩ := hodd
  suffices h : ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      n = p + q + r by
    obtain ⟨a, b, c, ha, hb, hc, hsum⟩ := h
    rcases le_total a b with hab | hba <;>
      rcases le_total b c with hbc | hcb <;>
      rcases le_total a c with hac | hca <;>
      first
        | refine ⟨a, b, c, ha, hb, hc, ?_, ?_, ?_⟩ <;> omega
        | refine ⟨a, c, b, ha, hc, hb, ?_, ?_, ?_⟩ <;> omega
        | refine ⟨b, a, c, hb, ha, hc, ?_, ?_, ?_⟩ <;> omega
        | refine ⟨b, c, a, hb, hc, ha, ?_, ?_, ?_⟩ <;> omega
        | refine ⟨c, a, b, hc, ha, hb, ?_, ?_, ?_⟩ <;> omega
        | refine ⟨c, b, a, hc, hb, ha, ?_, ?_, ?_⟩ <;> omega
  by_cases h7 : n = 7
  · subst h7
    exact ⟨2, 2, 3, Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩
  by_cases hbig : 10 ^ 27 ≤ n
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.three_odd_primes_ge_10pow27 n hbig hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
  · obtain ⟨p, q, r, hp, hq, hr, _, _, _, hsum⟩ :=
      WeakGoldbach.verified_three_odd_primes_to_8875e30 n
        (by omega) (by omega) hodd
    exact ⟨p, q, r, hp, hq, hr, hsum⟩
