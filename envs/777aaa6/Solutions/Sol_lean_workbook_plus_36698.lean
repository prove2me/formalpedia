-- Prove2me | solution 1 for lean_workbook_plus_36698
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:46:16.131294+00:00
-- url     : https://prove2.me/submissions/a100b58a-d680-4d2d-865f-20c93fe79a3e

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

private theorem divisor_count_prime_power (p k : ℕ) (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  rw [← ArithmeticFunction.sigma_zero_apply,
    ArithmeticFunction.sigma_zero_apply_prime_pow hp]

theorem eight_divisors_classification (n : ℕ) (hn : 0 < n) :
    n.divisors.card = 8 ↔
      (∃ p : ℕ, p.Prime ∧ n = p ^ 7) ∨
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q ^ 3) ∨
      (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
        p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p * q * r) := by
  constructor
  · intro h
    have he (p : ℕ) (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p := by
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp)
    have hprod : (∏ p ∈ n.primeFactors, (n.factorization p + 1)) = 8 := by
      rwa [Nat.card_divisors hn.ne'] at h
    have hrec : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n :=
      Nat.factorization_prod_pow_eq_self hn.ne'
    have hlow : 2 ^ n.primeFactors.card ≤ 8 := by
      rw [← hprod]
      exact Finset.pow_card_le_prod _ _ 2 (fun p hp => by have := he p hp; omega)
    have hcard : n.primeFactors.card ≤ 3 := by
      by_contra hc
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 4 ≤ n.primeFactors.card by omega)
      norm_num at hh
      omega
    interval_cases hc : n.primeFactors.card
    · have hs := Finset.card_eq_zero.mp hc
      simp [hs] at hprod
    · obtain ⟨p, hs⟩ := Finset.card_eq_one.mp hc
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hs])
      have hep : n.factorization p = 7 := by simpa [hs] using hprod
      left
      refine ⟨p, hp, ?_⟩
      simpa [hs, hep] using hrec.symm
    · obtain ⟨p, q, hpq, hs⟩ := Finset.card_eq_two.mp hc
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hs])
      have hq : q.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hs])
      have hep := he p (by simp [hs])
      have heq := he q (by simp [hs])
      have hprod2 : (n.factorization p + 1) * (n.factorization q + 1) = 8 := by
        simpa [hs, hpq] using hprod
      have hrec2 : p ^ n.factorization p * q ^ n.factorization q = n := by
        simpa [hs, hpq] using hrec
      right; left
      by_cases hep1 : n.factorization p = 1
      · have heq3 : n.factorization q = 3 := by nlinarith
        exact ⟨p, q, hp, hq, hpq, by simpa [hep1, heq3] using hrec2.symm⟩
      · have heq1 : n.factorization q = 1 := by
          by_contra hq1
          have hh := Nat.mul_le_mul
            (show 3 ≤ n.factorization p + 1 by omega)
            (show 3 ≤ n.factorization q + 1 by omega)
          omega
        have hep3 : n.factorization p = 3 := by nlinarith
        exact ⟨q, p, hq, hp, hpq.symm, by simpa [hep3, heq1, mul_comm] using hrec2.symm⟩
    · obtain ⟨p, q, r, hpq, hpr, hqr, hs⟩ := Finset.card_eq_three.mp hc
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hs])
      have hq : q.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hs])
      have hr : r.Prime := Nat.prime_of_mem_primeFactors (n := n) (by simp [hs])
      have hep := he p (by simp [hs])
      have heq := he q (by simp [hs])
      have her := he r (by simp [hs])
      have hprod3 : (n.factorization p + 1) * (n.factorization q + 1) *
          (n.factorization r + 1) = 8 := by
        simpa [hs, hpq, hpr, hqr, mul_assoc] using hprod
      have hep1 : n.factorization p = 1 := by
        have hh := Nat.mul_le_mul_left (n.factorization p + 1)
          (show 4 ≤ (n.factorization q + 1) * (n.factorization r + 1) by nlinarith)
        nlinarith
      have heq1 : n.factorization q = 1 := by
        have hh := Nat.mul_le_mul_left (n.factorization q + 1)
          (show 4 ≤ (n.factorization p + 1) * (n.factorization r + 1) by nlinarith)
        nlinarith
      have her1 : n.factorization r = 1 := by
        have hh := Nat.mul_le_mul_left (n.factorization r + 1)
          (show 4 ≤ (n.factorization p + 1) * (n.factorization q + 1) by nlinarith)
        nlinarith
      right; right
      refine ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, ?_⟩
      simpa [hs, hpq, hpr, hqr, hep1, heq1, her1, mul_assoc] using hrec.symm
  · rintro (⟨p, hp, rfl⟩ | ⟨p, q, hp, hq, hpq, rfl⟩ |
      ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr, rfl⟩)
    · exact divisor_count_prime_power p 7 hp
    · have hc : p.Coprime (q ^ 3) := ((Nat.coprime_primes hp hq).mpr hpq).pow_right 3
      rw [hc.card_divisors_mul, divisor_count_prime_power q 3 hq]
      have hcp : p.divisors.card = 2 := by
        simpa using divisor_count_prime_power p 1 hp
      rw [hcp]
    · have hpq' := (Nat.coprime_primes hp hq).mpr hpq
      have hpr' := (Nat.coprime_primes hp hr).mpr hpr
      have hqr' := (Nat.coprime_primes hq hr).mpr hqr
      rw [(hpr'.mul_left hqr').card_divisors_mul, hpq'.card_divisors_mul]
      have hcp : p.divisors.card = 2 := by simpa using divisor_count_prime_power p 1 hp
      have hcq : q.divisors.card = 2 := by simpa using divisor_count_prime_power q 1 hq
      have hcr : r.divisors.card = 2 := by simpa using divisor_count_prime_power r 1 hr
      rw [hcp, hcq, hcr]

theorem solution (n : ℕ) (hn : n > 0) (h : Finset.card (Nat.divisors n) = 8) :
    ∃ (p q r : ℕ), p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p ^ 7 ∨
      n = p * q ^ 3 ∨ n = p * q * r := by
  rcases (eight_divisors_classification n hn).mp h with
    ⟨p, hp, he⟩ | ⟨p, q, _hp, _hq, _hpq, he⟩ |
      ⟨p, q, r, _hp, _hq, _hr, _hpq, _hpr, _hqr, he⟩
  · exact ⟨p, 2, 2, Or.inl ⟨hp, Nat.prime_two, Nat.prime_two, he⟩⟩
  · exact ⟨p, q, 2, Or.inr (Or.inl he)⟩
  · exact ⟨p, q, r, Or.inr (Or.inr he)⟩
