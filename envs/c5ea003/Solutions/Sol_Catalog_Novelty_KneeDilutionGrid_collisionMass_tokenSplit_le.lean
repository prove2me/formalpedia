-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.collisionMass_tokenSplit_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:16:45.472862+00:00
-- url     : https://prove2.me/submissions/07a5e05e-0f51-4413-a99f-3872c6f9c5c9

-- Sol generated from Novelty/KneeCollisionBound.lean
import Mathlib
import Definitions.Def_Novelty_KneeCollisionBound
import Definitions.Def_Novelty_KneeDilutionGrid
import Theorems.Thm_Catalog_Novelty_KneeDilutionGrid_collisionMass_tokenSplit

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


lemma collisionMass_mono (p : ℕ → ℝ) : Monotone (collisionMass p) := by
  intro a b hab
  exact Finset.sum_le_sum_of_subset_of_nonneg (by simpa using hab) fun i _ _ => sq_nonneg _






/-! ### Sharpness -/




open Catalog.Novelty.KneeDilutionGrid in
theorem solution{r : ℕ} (hr : 0 < r) {p : ℕ → ℝ} {C : ℝ}
    (hbound : ∀ k, collisionMass p k ≤ C) (k : ℕ) :
    collisionMass (tokenSplit r p) k ≤ C / r := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hmod : k % r < r := Nat.mod_lt _ hr
  have hdm : r * (k / r) + k % r = k := Nat.div_add_mod k r
  have hle : k ≤ r * (k / r + 1) := by
    calc k = r * (k / r) + k % r := hdm.symm
      _ ≤ r * (k / r) + r := Nat.add_le_add_left hmod.le _
      _ = r * (k / r + 1) := by ring
  calc collisionMass (tokenSplit r p) k
      ≤ collisionMass (tokenSplit r p) (r * (k / r + 1)) := collisionMass_mono _ hle
    _ = collisionMass p (k / r + 1) / r := collisionMass_tokenSplit r hr p _
    _ ≤ C / r := div_le_div_of_nonneg_right (hbound _) hrR.le
