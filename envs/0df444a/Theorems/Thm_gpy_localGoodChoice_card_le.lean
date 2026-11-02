-- Prove2me | Theorems.Thm_gpy_localGoodChoice_card_le
-- name    : gpy_localGoodChoice_card_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:38:43.46339+00:00
-- url     : https://prove2.me/theorems/764f5a3b-3266-4696-96db-7e13c09b3055
-- title:
--   Local good-choice count is at most (k+1)^2
-- statement:
--   For any prime (indeed any natural number) p and any membership pattern, the local good-choice count — the number of pairs of optional coordinates satisfying the local good-pair condition at p — is at most (k+1)^2. The choice finset is a subfinset of all pairs of optional coordinates, of which there are (k+1)^2. This uniform O(1)-in-p bound is unconditional and elementary; it claims no asymptotic main term. Formalization Note: the statement is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY twisted absolute bounds: unconditional absolute/tail control for the twisted Mertens sums (local file GPYTwistedMertens.lean); the asymptotic twisted Mertens main term is NOT proved and NOT claimed.

import Mathlib
open Classical

theorem gpy_localGoodChoice_card_le {k : ℕ} (h : Fin k → ℕ) (i : Fin k) (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by sorry
