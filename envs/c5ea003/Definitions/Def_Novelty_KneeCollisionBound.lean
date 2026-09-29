-- Prove2me | Definitions.Def_Novelty_KneeCollisionBound
-- name    : Novelty_KneeCollisionBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:01.071524+00:00
-- url     : https://prove2.me/theorems/50ab1070-1999-4e95-b896-3eba4dd21ecc
-- title:
--   Aether Catalog definitions — Novelty_KneeCollisionBound
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KneeCollisionBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KneeCollisionBound.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.Novelty.KneeDilutionGrid

open Finset

/-- Collision (Rényi-2) mass of the first `k` attention weights. -/
def collisionMass (p : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ range k, p i ^ 2







/-! ### Sharpness -/



end Catalog.Novelty.KneeDilutionGrid


