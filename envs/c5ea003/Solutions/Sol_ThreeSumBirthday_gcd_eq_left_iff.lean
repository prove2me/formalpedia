-- Prove2me | solution 1 for ThreeSumBirthday.gcd_eq_left_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:33:04.055827+00:00
-- url     : https://prove2.me/submissions/6a285c2a-8521-4c3e-b789-022008dc2b85

import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy
open ThreeSumBirthday in
theorem solution {p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd s (p * q) = p ↔ (p ∣ s ∧ ¬ q ∣ s) := by
  constructor
  · intro h
    refine ⟨h ▸ Nat.gcd_dvd_left s (p * q), ?_⟩
    intro hqs
    -- `q ∣ s` and `q ∣ p*q` would put `q` into the gcd, i.e. `q ∣ p`
    have hqg : q ∣ Nat.gcd s (p * q) := Nat.dvd_gcd hqs ⟨p, by ring⟩
    rw [h] at hqg
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp hqg).symm
  · rintro ⟨hps, hqs⟩
    have hpd : p ∣ Nat.gcd s (p * q) := Nat.dvd_gcd hps ⟨q, rfl⟩
    have hgd : Nat.gcd s (p * q) ∣ p * q := Nat.gcd_dvd_right s (p * q)
    obtain ⟨k, hk⟩ := hpd
    rw [hk] at hgd
    have hp0 : p ≠ 0 := hp.ne_zero
    have hkq : k ∣ q := (mul_dvd_mul_iff_left hp0).mp hgd
    rcases hq.eq_one_or_self_of_dvd k hkq with h1 | h1
    · rw [hk, h1, mul_one]
    · exfalso
      refine hqs (dvd_trans ?_ (Nat.gcd_dvd_left s (p * q)))
      rw [hk, h1]
      exact ⟨p, by ring⟩
