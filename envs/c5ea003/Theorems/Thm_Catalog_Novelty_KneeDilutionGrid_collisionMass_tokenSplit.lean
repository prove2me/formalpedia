-- Prove2me | Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_collisionMass_tokenSplit
-- name    : Catalog.Novelty.KneeDilutionGrid.collisionMass_tokenSplit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:11:26.861835+00:00
-- url     : https://prove2.me/theorems/d44d7dbb-7a54-43db-a941-b7d357d9a727
-- title:
--   Dilution divides the collision mass by the tokens-per-word ratio, exactly.
-- statement:
--   Dilution divides the collision mass by the tokens-per-word ratio, exactly.
--
--   ```lean
--   theorem Catalog.Novelty.KneeDilutionGrid.collisionMass_tokenSplit(r : ℕ) (hr : 0 < r) (p : ℕ → ℝ) (m : ℕ) :
--       collisionMass (tokenSplit r p) (r * m) = collisionMass p m / r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KneeCollisionBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KneeCollisionBound.lean#L63

-- Thm stub generated from Novelty/KneeCollisionBound.lean
import Mathlib
import Definitions.Def_Novelty_KneeCollisionBound
import Definitions.Def_Novelty_KneeDilutionGrid

/-!
# An information-theoretic lower bound for the memory knee (NET-72, round 3)

`Novelty.KneeDilutionGrid` derived the knee of a diluted profile from the
tokens-per-word ratio.  That is a *mechanistic* explanation and it needs the
tokenizer.  This file gives a **tokenizer-free** lower bound for the knee in
terms of a single scalar statistic of the attention profile, its **collision
mass** (Rényi-2 mass) `collisionMass p k = ∑_{i<k} p i ^ 2`:

* `prefixMass_sq_le_collision` — Cauchy–Schwarz: `(∑_{i<k} p i)² ≤ k · ∑_{i<k} p i²`.
* `knee_ge_of_collision` — hence if the collision mass never exceeds `C`, then
  `knee p tau ≥ tau² / C`.  Flat (high-entropy, low-collision) attention forces a
  large knee; peaked attention permits a small one.
* `collisionMass_tokenSplit` — dilution by `r` divides the collision mass by `r`
  exactly, so the entropy bound is amplified by `r`
  (`dilution_amplifies_collision_bound`): the information-theoretic route
  reproduces the multiplicative law of `dilution_law` *without* referring to the
  tokenizer.  Two independent derivations of the same scaling.
* `collision_bound_sharp` — the bound is attained by the flat profile, so no
  better function of the collision mass exists.

Read against NET-72: the French cell is predicted to have a smaller collision
mass (flatter attention) than the English cell at the same context length, and
`knee ≥ tau²/C` then puts the knee beyond the arithmetic grid.  The bound is
measurable from attention maps alone, which makes it a falsifiable successor to
the tokens-per-word hypothesis.
-/

open Catalog.Novelty.KneeDilutionGrid

open Finset

theorem Catalog.Novelty.KneeDilutionGrid.collisionMass_tokenSplit(r : ℕ) (hr : 0 < r) (p : ℕ → ℝ) (m : ℕ) :
    collisionMass (tokenSplit r p) (r * m) = collisionMass p m / r := by sorry
