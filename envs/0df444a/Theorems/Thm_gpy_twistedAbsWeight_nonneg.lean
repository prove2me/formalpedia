-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_nonneg
-- name    : gpy_twistedAbsWeight_nonneg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:30:29.515781+00:00
-- url     : https://prove2.me/theorems/5c16006b-5236-48ec-ba47-21feae782b6c
-- title:
--   Absolute twisted weight is nonnegative
-- statement:
--   The absolute twisted weight at any natural number n, defined as the absolute value of the Möbius function times the twisted weight, is nonnegative. This is immediate from nonnegativity of absolute value, stated here in fully unfolded Mathlib terms. It claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_nonneg {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] (n : ℕ) :
    (0 : ℝ) ≤ abs ((ArithmeticFunction.moebius n : ℝ) * ((∏ p ∈ n.primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient n : ℕ) : ℝ))) := by sorry
