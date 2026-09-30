-- Prove2me | solution 1 for lean_workbook_plus_51141
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:24:23.133973+00:00
-- url     : https://prove2.me/submissions/7f1d44d5-c70f-431d-9b96-fbc481eb6cd5

import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

private theorem prime_times_exponent_le_power (p a : ℕ) (hp : 2 ≤ p) (ha : 0 < a) :
    p * a ≤ p ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  have hk : k + 1 ≤ p ^ k :=
    (Nat.succ_le_iff.mpr (Nat.lt_two_pow_self (n := k))).trans (Nat.pow_le_pow_left hp k)
  calc
    p * (k + 1) ≤ p * p ^ k := Nat.mul_le_mul_left p hk
    _ = p ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]

theorem multiplicative_positive_exponent_bound (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hmul : ∀ m n, m.Coprime n → f (m * n) = f m * f n)
    (hpow : ∀ p a, p.Prime → 0 < a → f (p ^ a) = p * f a) :
    ∀ n, 0 < n → f n ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    rw [Nat.multiplicative_factorization f hmul h1 hn0]
    calc
      n.factorization.prod (fun p a => f (p ^ a)) ≤
          n.factorization.prod (fun p a => p ^ a) := by
        apply Finset.prod_le_prod'
        intro p hp
        have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
        have ha : 0 < n.factorization p :=
          Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
        change f (p ^ n.factorization p) ≤ p ^ n.factorization p
        rw [hpow p (n.factorization p) hprime ha]
        exact (Nat.mul_le_mul_left p (ih (n.factorization p)
          (Nat.factorization_lt p hn0) ha)).trans
          (prime_times_exponent_le_power p (n.factorization p) hprime.two_le ha)
      _ = n := Nat.factorization_prod_pow_eq_self hn0

theorem arithmetic_function_exponent_bound (f : ArithmeticFunction ℕ)
    (hf : f.IsMultiplicative)
    (hpow : ∀ p a, p.Prime → 0 < a → f (p ^ a) = p * f a) (n : ℕ) : f n ≤ n := by
  by_cases hn : n = 0
  · subst n
    simp
  · exact multiplicative_positive_exponent_bound f hf.1
      (fun _ _ h => hf.map_mul_of_coprime h) hpow n (Nat.pos_of_ne_zero hn)

theorem prime_exponent_equality_unbounded (f : ℕ → ℕ) (h1 : f 1 = 1)
    (hpow : ∀ p a, p.Prime → 0 < a → f (p ^ a) = p * f a) (N : ℕ) :
    ∃ p, N ≤ p ∧ p.Prime ∧ f p = p := by
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes N
  refine ⟨p, hpN, hp, ?_⟩
  simpa [h1] using hpow p 1 hp (by decide)

theorem zero_exponent_law_impossible (f : ℕ → ℕ)
    (hf : f 1 = 1 ∧ ∀ p a : ℕ, Nat.Prime p → f (p ^ a) = p * f a) : False := by
  have h := hf.2 2 0 Nat.prime_two
  norm_num [hf.1] at h
  omega

theorem solution {f : ℕ → ℕ}
    (hf : f 1 = 1 ∧ ∀ p a : ℕ, Nat.Prime p → f (p ^ a) = p * f a) :
    ∀ n : ℕ, f n ≤ n := by
  exact (zero_exponent_law_impossible f hf).elim
