-- Prove2me | Theorems.Thm_gpy_twistedWeight_prime
-- name    : gpy_twistedWeight_prime
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:28:24.305307+00:00
-- url     : https://prove2.me/theorems/9abfcc32-c053-4196-b8f1-f163b1d63f4a
-- title:
--   Twisted weight at a prime
-- statement:
--   For a prime p, the twisted one-variable weight at p equals the local good-choice count at p divided by p - 1. The prime has a single prime factor, itself, and its totient is p - 1. This is an unconditional, elementary evaluation; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedWeight_prime {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] {p : ℕ} (hp : p.Prime) :
    ((∏ p ∈ p.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient p : ℕ) : ℝ)) = ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1) := by sorry
