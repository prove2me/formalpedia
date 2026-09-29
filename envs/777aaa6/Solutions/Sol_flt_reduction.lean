-- Prove2me | solution 1 for flt_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-11T08:30:48.919412+00:00
-- url     : https://prove2.me/submissions/8d82b80c-002d-4926-8540-f64604aec86a

import Theorems.Thm_flt_reduction
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic

theorem solution
    (h4 : ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → a ^ 4 + b ^ 4 ≠ c ^ 4)
    (hodd : ∀ (p : ℕ), p.Prime → 2 < p →
      ∀ (a b c : ℕ), 0 < a → 0 < b → 0 < c → a ^ p + b ^ p ≠ c ^ p)
    (n : ℕ) (hn : 3 ≤ n)
    (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ n + b ^ n ≠ c ^ n := by
  intro heq
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  obtain ⟨m, hm⟩ := hpn
  by_cases hp_gt2 : 2 < p
  · have ha' : 0 < a ^ m := Nat.one_le_pow m a ha
    have hb' : 0 < b ^ m := Nat.one_le_pow m b hb
    have hc' : 0 < c ^ m := Nat.one_le_pow m c hc
    have key : (a ^ m) ^ p + (b ^ m) ^ p = (c ^ m) ^ p := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm m p, ← hm]; exact heq
    exact hodd p hp hp_gt2 (a ^ m) (b ^ m) (c ^ m) ha' hb' hc' key
  · have hp2 : p = 2 := by have := hp.two_le; omega
    subst hp2
    have hm_ge2 : 2 ≤ m := by omega
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
    obtain ⟨k, hk⟩ := hqm
    by_cases hq_gt2 : 2 < q
    · have hn_qk : n = q * (2 * k) := by
        rw [hm, hk]; exact (mul_left_comm q 2 k).symm
      have ha' : 0 < a ^ (2 * k) := Nat.one_le_pow (2 * k) a ha
      have hb' : 0 < b ^ (2 * k) := Nat.one_le_pow (2 * k) b hb
      have hc' : 0 < c ^ (2 * k) := Nat.one_le_pow (2 * k) c hc
      have key : (a ^ (2 * k)) ^ q + (b ^ (2 * k)) ^ q = (c ^ (2 * k)) ^ q := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, mul_comm (2 * k) q, ← hn_qk]; exact heq
      exact hodd q hq hq_gt2 (a ^ (2 * k)) (b ^ (2 * k)) (c ^ (2 * k)) ha' hb' hc' key
    · have hq2 : q = 2 := by have := hq.two_le; omega
      subst hq2
      have hn4k : n = 4 * k := by omega
      have ha' : 0 < a ^ k := Nat.one_le_pow k a ha
      have hb' : 0 < b ^ k := Nat.one_le_pow k b hb
      have hc' : 0 < c ^ k := Nat.one_le_pow k c hc
      have key4 : (a ^ k) ^ 4 + (b ^ k) ^ 4 = (c ^ k) ^ 4 := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, (show k * 4 = n by omega)]; exact heq
      exact h4 (a ^ k) (b ^ k) (c ^ k) ha' hb' hc' key4
