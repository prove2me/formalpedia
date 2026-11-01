-- Prove2me | Theorems.Thm_gpy_twistedLocal_term_le
-- name    : gpy_twistedLocal_term_le
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T05:42:27.732659+00:00
-- url     : https://prove2.me/theorems/b5362daf-6ece-49cc-a35a-69c7327e6255
-- title:
--   One local term of the twisted Euler product is at most 2 (k+1)^2 / p
-- statement:
--   For a prime p, the local twisted term (local good-choice count at p) / (p - 1) is at most 2 (k+1)^2 / p, from the uniform local-count bound (k+1)^2. This is an unconditional elementary bound, one step of the twisted absolute-bound argument. No defect smallness is claimed.
-- source:
--   GPY defect smallness (GPYDefectSmall.lean), restated into Mathlib-only terms

import Mathlib
open Classical

theorem gpy_twistedLocal_term_le {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (hd he : Prop) [Decidable hd] [Decidable he]
    {p : ℕ} (hp : p.Prime) :
    ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ) / ((p : ℝ) - 1)
      ≤ 2 * ((k : ℝ) + 1) ^ 2 / (p : ℝ) := by sorry
