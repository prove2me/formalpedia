-- Prove2me | solution 1 for lean_workbook_plus_34064
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:37.601102+00:00
-- url     : https://prove2.me/submissions/16fc0b5d-e369-49c8-a6c6-4ffe6dc468a3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Tactic

namespace TripleGcdLinearCombination

theorem exists_positive_coefficient (a b c : ℤ) (ha : a ≠ 0)
    (hcoprime : (a.gcd b : ℤ).gcd c = 1) :
    ∃ k : ℕ, 0 < k ∧ a.gcd (b + (k : ℤ) * c) = 1 := by
  classical
  let s : Finset ℕ := a.natAbs.primeFactors.filter (fun p : ℕ => ¬ (p : ℤ) ∣ b)
  let k : ℕ := ∏ p ∈ s, p
  have hpos : 0 < k := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.pos
  refine ⟨k, hpos, ?_⟩
  change Nat.Coprime a.natAbs (b + (k : ℤ) * c).natAbs
  apply Nat.coprime_of_dvd
  intro p hp hpa hpv
  have hpaZ : (p : ℤ) ∣ a := Int.natCast_dvd.mpr hpa
  have hpvZ : (p : ℤ) ∣ b + (k : ℤ) * c := Int.natCast_dvd.mpr hpv
  by_cases hpb : (p : ℤ) ∣ b
  · have hpk : ¬ p ∣ k := by
      apply hp.prime.not_dvd_finset_prod
      intro q hq hpq
      obtain ⟨hqprime, hqnot⟩ := Finset.mem_filter.mp hq
      have hqprime' := (Nat.mem_primeFactors.mp hqprime).1
      have hpqeq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqprime').mp hpq
      exact hqnot (hpqeq ▸ hpb)
    have hpmulZ : (p : ℤ) ∣ (k : ℤ) * c := by
      have h := dvd_sub hpvZ hpb
      simpa using h
    have hpmul : p ∣ k * c.natAbs := by
      simpa [Int.natAbs_mul] using Int.natCast_dvd.mp hpmulZ
    have hpc : p ∣ c.natAbs := (hp.dvd_mul.mp hpmul).resolve_left hpk
    have hpgcd : (p : ℤ) ∣ (a.gcd b : ℤ) := Int.dvd_coe_gcd hpaZ hpb
    have hpone : (p : ℤ) ∣ (1 : ℤ) := by
      simpa [hcoprime] using Int.dvd_coe_gcd hpgcd (Int.natCast_dvd.mpr hpc)
    have hponeN : p ∣ 1 := by exact_mod_cast hpone
    exact hp.not_dvd_one hponeN
  · have hps : p ∈ s := by
      exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
        ⟨hp, hpa, Int.natAbs_ne_zero.mpr ha⟩, hpb⟩
    have hpk : p ∣ k := Finset.dvd_prod_of_mem (fun q : ℕ => q) hps
    have hpkZ : (p : ℤ) ∣ (k : ℤ) := Int.natCast_dvd_natCast.mpr hpk
    have hpb' : (p : ℤ) ∣ b := by
      have h := dvd_sub hpvZ (dvd_mul_of_dvd_left hpkZ c)
      simpa using h
    exact hpb hpb'

theorem full_written_claim (a b c : ℤ) (ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hcoprime : (a.gcd b : ℤ).gcd c = 1) :
    ∃ k : ℤ, 0 < k ∧ a.gcd (b + k * c) = 1 := by
  obtain ⟨k, hk, h⟩ := exists_positive_coefficient a b c (ne_of_gt ha) hcoprime
  exact ⟨k, by exact_mod_cast hk, h⟩

end TripleGcdLinearCombination

theorem solution {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
    (hab : a.gcd b = 1) (hbc : a.gcd c = 1) (hca : b.gcd c = 1) :
    ∃ k : ℤ, a.gcd (b + k * c) = 1 := by
  have htriple : (a.gcd b : ℤ).gcd c = 1 := by simp [hab]
  obtain ⟨k, _, h⟩ := TripleGcdLinearCombination.exists_positive_coefficient a b c habc.1 htriple
  exact ⟨k, h⟩

#print axioms TripleGcdLinearCombination.exists_positive_coefficient
#print axioms TripleGcdLinearCombination.full_written_claim
