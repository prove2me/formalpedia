-- Prove2me | Theorems.Thm_gpy_twistedAbsWeight_one
-- name    : gpy_twistedAbsWeight_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T16:41:24.033072+00:00
-- url     : https://prove2.me/theorems/10ca083f-aeab-4ebf-8402-432fca9581b8
-- title:
--   Absolute twisted weight at 1 equals 1
-- statement:
--   The absolute twisted weight at 1 equals 1, since the Möbius function at 1 is 1 and the twisted weight at 1 is 1. This is an unconditional, elementary normalization fact, stated in fully unfolded Mathlib terms. It claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedAbsWeight_one {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] :
    abs ((ArithmeticFunction.moebius 1 : ℝ) * ((∏ p ∈ (1 : ℕ).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient 1 : ℕ) : ℝ))) = 1 := by sorry
