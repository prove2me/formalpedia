-- Prove2me | solution 1 for ThreeSumBirthday.gcd_semiprime_classification
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T05:42:57.484738+00:00
-- url     : https://prove2.me/submissions/5f52c1fc-bc81-47ef-bffd-999f2659db38

import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy
theorem solution {p q s : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Nat.gcd s (p * q) =
      if p ∣ s then (if q ∣ s then p * q else p) else (if q ∣ s then q else 1) := by
  -- `gcd s (p q) = gcd s p · gcd s q`, and each factor is `p` or `1`
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hP : ∀ r : ℕ, r.Prime → Nat.gcd s r = if r ∣ s then r else 1 := by
    intro r hr
    split_ifs with h
    · exact Nat.gcd_eq_right h
    · rw [Nat.gcd_comm]
      exact (Nat.Prime.coprime_iff_not_dvd hr).mpr h
  rw [Nat.Coprime.gcd_mul s hcop, hP p hp, hP q hq]
  split_ifs <;> simp
