-- Prove2me | solution 1 for coprime_fifth_power_factor
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T08:50:31.224003+00:00
-- url     : https://prove2.me/submissions/970a7851-7181-4a53-aa74-da37be0df8f2

import Theorems.Thm_coprime_fifth_power_factor
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

theorem solution (a b c : ℤ) (hab : Int.gcd a b = 1) (heq : a * b = c ^ 5) :
    ∃ d : ℤ, a = d ^ 5 := by
  have hcop : Nat.Coprime a.natAbs b.natAbs := hab
  have heq_nat : a.natAbs * b.natAbs = c.natAbs ^ 5 := by
    have := congr_arg Int.natAbs heq
    simp only [Int.natAbs_mul, Int.natAbs_pow] at this; exact this
  by_cases ha0 : a = 0
  · exact ⟨0, by simp [ha0]⟩
  have hana : a.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr ha0
  by_cases hb0 : b = 0
  · have ha1 : a.natAbs = 1 := by
      have h := hab
      simp only [Int.gcd, hb0, Int.natAbs_zero, Nat.gcd_zero_right] at h
      exact h
    rcases Int.natAbs_eq a with ha | ha
    · have haeq : a = 1 := by rw [ha, ha1]; norm_cast
      exact ⟨1, by rw [haeq]; ring⟩
    · have haeq : a = -1 := by rw [ha, ha1]; norm_cast
      exact ⟨-1, by rw [haeq]; ring⟩
  have hbnz : b.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hb0
  have hexp : ∀ p : ℕ, 5 ∣ a.natAbs.factorization p := by
    intro p
    by_cases hp : p.Prime
    · have hfact_p : a.natAbs.factorization p + b.natAbs.factorization p =
          5 * c.natAbs.factorization p := by
        have h : (a.natAbs.factorization + b.natAbs.factorization) p =
            (5 • c.natAbs.factorization) p := by
          rw [← Nat.factorization_mul hana hbnz, heq_nat, Nat.factorization_pow]
        simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
        exact h
      rcases Nat.eq_zero_or_pos (a.natAbs.factorization p) with ha | ha
      · exact ha ▸ dvd_zero 5
      · have hpa : p ∣ a.natAbs := Nat.dvd_of_factorization_pos ha.ne'
        have hnpb : ¬(p ∣ b.natAbs) := fun hpb => by
          have hle : p ≤ 1 := Nat.le_of_dvd one_pos (hcop ▸ Nat.dvd_gcd hpa hpb)
          exact absurd hle (not_le.mpr (Nat.Prime.one_lt hp))
        have hbp0 : b.natAbs.factorization p = 0 := by
          by_contra h; exact hnpb (Nat.dvd_of_factorization_pos h)
        rw [hbp0, add_zero] at hfact_p
        exact ⟨c.natAbs.factorization p, hfact_p⟩
    · simp only [Nat.factorization_eq_zero_of_non_prime _ hp]
      exact dvd_zero 5
  set d_nat := a.natAbs.factorization.prod (fun q k => q ^ (k / 5))
  have hd5 : d_nat ^ 5 = a.natAbs := by
    show (a.natAbs.factorization.prod (fun q k => q ^ (k / 5))) ^ 5 = a.natAbs
    -- Rewrite only the RHS to avoid mangling the LHS factorization
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hana]
    -- Goal: (f.prod (fun q k => q^(k/5)))^5 = f.prod (·^·)
    -- where f = a.natAbs.factorization
    -- Use change (definitional equality) to convert Finsupp.prod → Finset.prod
    change a.natAbs.factorization.support.prod (fun p => p ^ (a.natAbs.factorization p / 5)) ^ 5 =
           a.natAbs.factorization.support.prod (fun p => p ^ a.natAbs.factorization p)
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p _
    rw [← pow_mul]
    congr 1
    exact Nat.div_mul_cancel (hexp p)
  rcases Int.natAbs_eq a with ha | ha
  · exact ⟨d_nat, by
      have h1 : (d_nat : ℤ) ^ 5 = (a.natAbs : ℤ) := by exact_mod_cast hd5
      rw [ha]; exact h1.symm⟩
  · exact ⟨-(d_nat : ℤ), by
      have h1 : (d_nat : ℤ) ^ 5 = (a.natAbs : ℤ) := by exact_mod_cast hd5
      rw [ha, ← h1]; ring⟩
