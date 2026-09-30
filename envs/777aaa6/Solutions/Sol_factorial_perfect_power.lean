-- Prove2me | solution 1 for factorial_perfect_power
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:11:40.005168+00:00
-- url     : https://prove2.me/submissions/cbc9946b-7d2b-4609-bcb7-0a67126325fc

import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Set.Finite.Basic

private theorem factorial_prime_multiplicity (n p : ℕ) (hp : p.Prime)
    (hpn : p ≤ n) (hnp : n < 2 * p) : emultiplicity p n.factorial = 1 := by
  have hnpp : n < p ^ 2 := by
    calc
      n < 2 * p := hnp
      _ ≤ p * p := Nat.mul_le_mul_right p hp.two_le
      _ = p ^ 2 := (pow_two p).symm
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow' (by decide) hnpp
  have hdiv : n / p = 1 := Nat.div_eq_of_lt_le (by simpa using hpn) hnp
  rw [hp.emultiplicity_factorial hlog]
  norm_num [hdiv]

private theorem factorial_ne_perfect_power (n m k : ℕ)
    (hn : 1 ≤ n) (hm : 2 ≤ m) (hk : 2 ≤ k) : n.factorial ≠ m ^ k := by
  intro heq
  have hn2 : 2 ≤ n := by
    by_contra h
    have hn1 : n = 1 := by omega
    have hpow : 1 < m ^ k := Nat.one_lt_pow (by omega) hm
    simp only [hn1, Nat.factorial_one] at heq
    omega
  obtain ⟨p, hp, hhalf, hupper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hpn : p ≤ n := by omega
  have hnp : n < 2 * p := by omega
  have hval := factorial_prime_multiplicity n p hp hpn hnp
  have hpdvd : p ∣ m ^ k := by
    rw [← heq]
    exact Nat.dvd_factorial hp.pos hpn
  have hpm : p ∣ m := hp.dvd_of_dvd_pow hpdvd
  have hsq : p ^ 2 ∣ n.factorial := by
    rw [heq]
    exact (pow_dvd_pow_of_dvd hpm 2).trans (Nat.pow_dvd_pow m hk)
  have hle := pow_dvd_iff_le_emultiplicity.mp hsq
  rw [hval] at hle
  exact (show ¬ (2 : ℕ∞) ≤ 1 by decide) hle

theorem solution :
    {(n, m, k) : ℕ × ℕ × ℕ |
      1 ≤ n ∧ 2 ≤ m ∧ 2 ≤ k ∧ n.factorial = m ^ k}.Finite := by
  have hempty : {(n, m, k) : ℕ × ℕ × ℕ |
      1 ≤ n ∧ 2 ≤ m ∧ 2 ≤ k ∧ n.factorial = m ^ k} = ∅ := by
    ext ⟨n, m, k⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hn, hm, hk, heq⟩
    exact factorial_ne_perfect_power n m k hn hm hk heq
  rw [hempty]
  exact Set.finite_empty

#print axioms solution
