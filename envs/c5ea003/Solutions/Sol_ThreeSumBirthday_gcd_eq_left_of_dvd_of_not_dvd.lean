-- Prove2me | solution 1 for ThreeSumBirthday.gcd_eq_left_of_dvd_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:13:37.486294+00:00
-- url     : https://prove2.me/submissions/57c193db-a3aa-49f2-be7b-02475d444302

import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy
theorem solution {p q s : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hps : p ∣ s) (hqs : ¬ q ∣ s) : Nat.gcd s (p * q) = p := by
  -- `p ≠ q`, since one divides `s` and the other does not
  have hne : p ≠ q := by
    rintro rfl
    exact hqs hps
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
  -- `gcd s (p q) = gcd s p · gcd s q = p · 1`
  rw [Nat.Coprime.gcd_mul s hcop, Nat.gcd_eq_right hps]
  have hsq : Nat.gcd s q = 1 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqs)
  rw [hsq, mul_one]
