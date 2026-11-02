-- Prove2me | Theorems.Thm_gpy_sum_truncSet_twistedAbsWeight_eq_prod
-- name    : gpy_sum_truncSet_twistedAbsWeight_eq_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:43:52.673493+00:00
-- url     : https://prove2.me/theorems/153625d9-f69b-402f-a6be-6afa80df8c87
-- title:
--   Truncated Euler product for the absolute twisted weight
-- statement:
--   For any finset S of primes, the sum of the absolute twisted weight over the truncated set of numbers whose prime factors lie in S with exponents at most 2 factors exactly as the product over p in S of the local sums 1 + c_p/(p-1), where c_p is the local good-choice count at p. This is the truncated Euler product for a multiplicative weight, proved unconditionally; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_sum_truncSet_twistedAbsWeight_eq_prod {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    ∑ d ∈ (Finset.range (∏ p ∈ S, p ^ 2 + 1)).filter (fun d =>
    1 ≤ d ∧ ∀ p ∈ d.primeFactors, p ∈ S ∧ d.factorization p ≤ 2), abs ((ArithmeticFunction.moebius d : ℝ) * ((∏ p ∈ d.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient d : ℕ) : ℝ))) = ∏ p ∈ S, (1 + ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1)) := by sorry
