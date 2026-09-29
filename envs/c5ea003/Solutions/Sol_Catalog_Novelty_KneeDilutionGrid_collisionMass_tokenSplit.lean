-- Prove2me | solution 1 for Catalog.Novelty.KneeDilutionGrid.collisionMass_tokenSplit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T18:15:21.758201+00:00
-- url     : https://prove2.me/submissions/19a47641-9f5b-4350-a726-a602eed9212f

-- Sol generated from Novelty/KneeCollisionBound.lean
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




open Catalog.Novelty.KneeDilutionGrid in
theorem solution(r : ℕ) (hr : 0 < r) (p : ℕ → ℝ) (m : ℕ) :
    collisionMass (tokenSplit r p) (r * m) = collisionMass p m / r := by
  have hrR : (r : ℝ) ≠ 0 := by positivity
  induction m with
  | zero => simp [collisionMass]
  | succ m ih =>
      have h1 : r * (m + 1) = r * m + r := by ring
      rw [h1]
      unfold collisionMass at *
      rw [Finset.sum_range_add, ih, Finset.sum_range_succ]
      have hblock : ∑ i ∈ range r, tokenSplit r p (r * m + i) ^ 2 = p m ^ 2 / r := by
        have h : ∀ i ∈ range r, tokenSplit r p (r * m + i) ^ 2 = (p m / r) ^ 2 := by
          intro i hi
          have hir : i < r := mem_range.1 hi
          simp only [tokenSplit]
          rw [Nat.mul_add_div hr, Nat.div_eq_of_lt hir]
          simp
        rw [Finset.sum_congr rfl h, Finset.sum_const, card_range, nsmul_eq_mul]
        field_simp
      rw [hblock]
      ring
