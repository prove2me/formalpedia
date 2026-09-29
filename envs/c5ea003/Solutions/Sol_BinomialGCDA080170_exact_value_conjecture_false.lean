-- Prove2me | solution 1 for BinomialGCDA080170.exact_value_conjecture_false
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T10:39:32.052865+00:00
-- url     : https://prove2.me/submissions/65f2ac3e-3924-4434-96b9-ef551d6d1d2e

import Mathlib
import Definitions.Def_Novelty_BinomialGCDA080170
open BinomialGCDA080170 in
theorem solution :
    ¬ (∀ k, 2 ≤ k → binomGCD k = stephanP (k + 1)) := by
  intro h
  -- the conjecture fails at `k = 11`
  have h11 : binomGCD 11 = stephanP 12 := h 11 (by norm_num)
  -- `stephanP 12 = max(2², 3¹) = 4`
  have hpf : Nat.primeFactors 12 = {2, 3} := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num), Nat.prime_two.primeFactors,
      Nat.prime_three.primeFactors]
    decide
  have hf2 : Nat.factorization 12 2 = 2 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  have hf3 : Nat.factorization 12 3 = 1 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.prime_three.factorization_self, Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rfl
  have hS : stephanP 12 = 4 := by
    unfold stephanP
    simp only [hpf, Finset.sup_insert, Finset.sup_singleton, hf2, hf3]
    decide
  -- but `binomGCD 11` divides `C(55, 11)`, which is `≡ 2 (mod 4)`
  have hdvd : binomGCD 11 ∣ Nat.choose (5 * 11) 11 := by
    unfold binomGCD
    exact Finset.gcd_dvd (f := fun q => Nat.choose (q * 11) 11)
      (Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩)
  have hc : ¬ 4 ∣ Nat.choose (5 * 11) 11 := by
    rw [Nat.choose_eq_factorial_div_factorial (by norm_num)]
    decide +kernel
  rw [h11, hS] at hdvd
  exact hc hdvd
