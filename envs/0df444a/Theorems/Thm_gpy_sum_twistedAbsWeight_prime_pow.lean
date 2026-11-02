-- Prove2me | Theorems.Thm_gpy_sum_twistedAbsWeight_prime_pow
-- name    : gpy_sum_twistedAbsWeight_prime_pow
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:41:47.888684+00:00
-- url     : https://prove2.me/theorems/5076233e-d0f5-433f-9822-aa4fd23bdc50
-- title:
--   Local absolute-weight sum at prime powers is 1 + c_p/(p-1)
-- statement:
--   For a prime p, the sum of the absolute twisted weight over p^j for j = 0, 1, 2 equals 1 + c_p/(p-1), where c_p is the local good-choice count at p. The j = 0 term is 1, the j = 1 term is c_p/(p-1), and the j = 2 term is 0 since the Möbius function vanishes at p^2. This is an unconditional, elementary local computation; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_sum_twistedAbsWeight_prime_pow {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {p : ℕ} (hp : p.Prime) :
    ∑ j ∈ Finset.range 3, abs ((ArithmeticFunction.moebius (p ^ j) : ℝ) * ((∏ p ∈ (p ^ j).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient (p ^ j) : ℕ) : ℝ))) = 1 + ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1) := by sorry
