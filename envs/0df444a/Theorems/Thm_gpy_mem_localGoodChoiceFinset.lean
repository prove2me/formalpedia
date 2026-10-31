-- Prove2me | Theorems.Thm_gpy_mem_localGoodChoiceFinset
-- name    : gpy_mem_localGoodChoiceFinset
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:21:24.565074+00:00
-- url     : https://prove2.me/theorems/2428bff3-3e9a-4c1b-b1fa-f51a6a3ba8f6
-- title:
--   Membership in the local choice finset, unfolded
-- statement:
--   A pair of optional coordinates lies in the local choice finset at a prime p exactly when its some-pattern matches the divisibility pattern, all coordinates receiving p have congruent shifts modulo p, and none is congruent to h i modulo p. Formalization Note: the local choice finset is written out in Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_mem_localGoodChoiceFinset {k : ℕ} {h : Fin k → ℕ} {i : Fin k}
    {p : ℕ} {hd he : Prop} [Decidable hd] [Decidable he]
    {ab : Option (Fin k) × Option (Fin k)} :
    ab ∈ (Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])) ↔
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])  := by sorry
