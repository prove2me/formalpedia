-- Prove2me | Theorems.Thm_gpy_twistedWeight_one
-- name    : gpy_twistedWeight_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T16:38:40.410617+00:00
-- url     : https://prove2.me/theorems/a8d26b91-7776-4a8b-be1b-fa27ec23456c
-- title:
--   Twisted weight at 1 equals 1
-- statement:
--   For any pattern of shifts, any fixed coordinate and any membership pattern, the twisted one-variable weight at 1 equals 1: the empty prime product is 1 and the totient of 1 is 1. This is an elementary normalization fact about the twisted weight, stated here in fully unfolded Mathlib terms with no local definitions. It is an absolute, unconditional statement; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_twistedWeight_one {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (hd he : Prop) [Decidable hd] [Decidable he] :
    ((∏ p ∈ (1 : ℕ).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ)) / ((Nat.totient 1 : ℕ) : ℝ)) = 1 := by sorry
