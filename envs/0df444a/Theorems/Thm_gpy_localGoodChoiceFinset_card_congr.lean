-- Prove2me | Theorems.Thm_gpy_localGoodChoiceFinset_card_congr
-- name    : gpy_localGoodChoiceFinset_card_congr
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T02:53:11.393755+00:00
-- url     : https://prove2.me/theorems/7d9d4fad-58c6-449c-b6be-c4c08bb792f7
-- title:
--   Local good-choice count depends only on the membership pattern
-- statement:
--   The cardinality of the local good-choice finset at a prime p depends only on the truth values of the two membership propositions, so replacing them by equivalent propositions leaves the count unchanged. This is an unconditional elementary lemma about the finite local count.
-- source:
--   GPY monomial joint (GPYMonomialJoint.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_localGoodChoiceFinset_card_congr {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} {hd he hd' he' : Prop} [Decidable hd] [Decidable he]
    [Decidable hd'] [Decidable he'] (h1 : hd ↔ hd') (h2 : he ↔ he') :
    ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card
      = ((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
      (ab.1.isSome ↔ hd') ∧ (ab.2.isSome ↔ he') ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))).card := by sorry
