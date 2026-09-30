-- Prove2me | solution 1 for lean_workbook_plus_56800
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:42:56.551033+00:00
-- url     : https://prove2.me/submissions/48b538be-dfd8-42d3-b542-f202a6617f1c

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Finite.Basic

theorem odd_prime_divisor_of_not_two_power (a : ℕ)
    (ha : ¬ ∃ k : ℕ, a + 1 = 2 ^ k) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ p ∣ a + 1 := by
  obtain ⟨k, m, hm, heq⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : a + 1 ≠ 0)
  have hm1 : m ≠ 1 := by
    intro h
    exact ha ⟨k, by simpa only [h, mul_one] using heq⟩
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    have := Nat.mod_eq_zero_of_dvd hpm
    have := Nat.odd_iff.mp hm
    omega
  refine ⟨p, hp, hp.odd_of_ne_two hp2, ?_⟩
  rw [heq]
  exact dvd_mul_of_dvd_right hpm _

theorem prime_power_self_exponent_valuation (a p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hpa : p ∣ a + 1) (k : ℕ) :
    padicValNat p (a ^ (p ^ k) + 1) = padicValNat p (a + 1) + k := by
  letI : Fact p.Prime := ⟨hp⟩
  have hna : ¬ p ∣ a := by
    intro h
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right h).mpr hpa)
  simpa only [one_pow, padicValNat.prime_pow] using
    padicValNat.pow_add_pow hodd hpa hna (hodd.pow : Odd (p ^ k))

theorem prime_power_self_exponent_divisibility (a p : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hpa : p ∣ a + 1) (k : ℕ) :
    p ^ k ∣ a ^ (p ^ k) + 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply (padicValNat_dvd_iff_le (by omega : a ^ (p ^ k) + 1 ≠ 0)).mpr
  rw [prime_power_self_exponent_valuation a p hp hodd hpa k]
  omega

theorem infinite_self_dividing_powers (a : ℕ)
    (ha : ¬ ∃ k : ℕ, a + 1 = 2 ^ k) :
    Set.Infinite {n : ℕ | 0 < n ∧ Odd n ∧ n ∣ a ^ n + 1} := by
  obtain ⟨p, hp, hodd, hpa⟩ := odd_prime_divisor_of_not_two_power a ha
  apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => p ^ k)
    (Nat.pow_right_injective hp.two_le)
  intro k
  exact ⟨pow_pos hp.pos k, hodd.pow,
    prime_power_self_exponent_divisibility a p hp hodd hpa k⟩

theorem solution (a : ℕ) (ha : ¬ ∃ k : ℕ, a + 1 = 2 ^ k) :
    ∃ n : ℕ, n ∣ a ^ n + 1 := by
  obtain ⟨n, hn⟩ := (infinite_self_dividing_powers a ha).nonempty
  exact ⟨n, hn.2.2⟩
