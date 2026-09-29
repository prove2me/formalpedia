-- Prove2me | Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_collision_bound_sharp
-- name    : Catalog.Novelty.KneeDilutionGrid.collision_bound_sharp
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:11:29.554412+00:00
-- url     : https://prove2.me/theorems/d9df2d65-b0f0-45c0-b0fd-5288c5a9fc2f
-- title:
--   The entropy bound is sharp.
-- statement:
--   **The entropy bound is sharp.**  The flat probability profile on `n` keys has
--   collision mass at most `1 / n`, bar `tau = 1`, knee exactly `n`, and the bound
--   `tau² / C = n`.  Hence no function of the collision mass can give a better
--   lower bound than `knee ≥ tau² / C`.
--
--   ```lean
--   theorem Catalog.Novelty.KneeDilutionGrid.collision_bound_sharp(n : ℕ) (hn : 0 < n) :
--       (∀ k, collisionMass (scaled (1 / n) n) k ≤ 1 / n) ∧
--         knee (scaled (1 / n) n) 1 = n ∧ (1 : ℝ) ^ 2 / (1 / n) = (n : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KneeCollisionBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KneeCollisionBound.lean#L131

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








/-! ### Sharpness -/

theorem Catalog.Novelty.KneeDilutionGrid.collision_bound_sharp(n : ℕ) (hn : 0 < n) :
    (∀ k, collisionMass (scaled (1 / n) n) k ≤ 1 / n) ∧
      knee (scaled (1 / n) n) 1 = n ∧ (1 : ℝ) ^ 2 / (1 / n) = (n : ℝ) := by sorry
