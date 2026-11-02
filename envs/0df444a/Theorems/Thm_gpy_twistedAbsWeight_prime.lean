-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_prime
-- name    : gpy_twistedAbsWeight_prime
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:34:35.470601+00:00
-- url     : https://prove2.me/theorems/189926a9-b4b3-4310-9fe2-d19350344a8b
-- title:
--   Absolute twisted weight at a prime
-- statement:
--   For a prime p, the absolute twisted weight at p equals the local good-choice count at p divided by p - 1. The Möbius function at a prime is -1, whose absolute value is 1, and the twisted weight at a prime is the local count over p - 1, a nonnegative quantity. This is an unconditional, elementary evaluation; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_prime {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {p : ℕ} (hp : p.Prime) :
    abs ((ArithmeticFunction.moebius p : ℝ) * ((∏ p ∈ p.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient p : ℕ) : ℝ))) = ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1) := by sorry
