-- Prove2me | Definitions.Def_Bridges_GL3TopCycleRobustness
-- name    : Bridges_GL3TopCycleRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:42.545167+00:00
-- url     : https://prove2.me/theorems/c544b789-7e4c-43c8-a80b-c82004b0e375
-- title:
--   Aether Catalog definitions — Bridges_GL3TopCycleRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3TopCycleRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3TopCycleRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL3 Tropical Satake Certified Robustness for Top-Cycle Classifiers

This module formalizes certified robustness theorems for tournament-valued classifiers
built from pairwise score comparisons. The key insight is that robustness of the
Condorcet winner (equivalently, the singleton Smith set / top cycle) under L∞
perturbations follows from uniform pairwise margin domination, with certified radius
`margin / (2 * K * d)` where `K` is the coordinatewise Lipschitz constant and `d`
is the input dimension.

The development proceeds in layers:
1. Basic L∞ → ℓ¹ norm estimate on `Fin d`
2. Score perturbation bounds from coordinatewise Lipschitz continuity
3. Pairwise margin preservation under bounded perturbations
4. Condorcet winner / Smith singleton stability
5. General dominance cut preservation
6. GL3 specialization to `Fin 3`

## Mathematical significance

This result bridges tropical Hecke score geometry with social choice theory:
the same `margin / (2*K*d)` radius that controls binary certified robustness
also governs the stability of tournament solution concepts (Condorcet winners,
Smith sets, dominance cuts) under score perturbations.
-/


open scoped BigOperators

/-! ## Core definitions -/


/-- A Condorcet winner beats every other class in pairwise comparison. -/
def CondorcetWinner {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℝ) (c : α) : Prop :=
  ∀ j, j ≠ c → score j < score c

/-- In a tournament, a Condorcet winner is exactly a singleton Smith set.
    This definition captures that equivalence as our interface. -/
def IsSmithSingleton {α : Type*} [Fintype α] [DecidableEq α]
    (score : α → ℝ) (c : α) : Prop :=
  CondorcetWinner score c

/-- Coordinatewise Lipschitz bound: each score function satisfies
    `|s i x - s i y| ≤ K * ∑ k, |x k - y k|`. -/
def CoordwiseLipschitz {α : Type*} (d : ℕ)
    (s : α → (Fin d → ℝ) → ℝ) (K : ℝ) : Prop :=
  ∀ i x y, |s i x - s i y| ≤ K * ∑ k : Fin d, |x k - y k|

/-- L∞ ball of radius `r`: every coordinate has absolute value at most `r`. -/
def LinftyBall {d : ℕ} (r : ℝ) (δ : Fin d → ℝ) : Prop :=
  ∀ k, |δ k| ≤ r

/-- Pairwise margin between classes `i` and `j` at input `x`. -/
def pairMargin {α β : Type*} (s : α → β → ℝ) (x : β) (i j : α) : ℝ :=
  s i x - s j x

/-! ## Auxiliary lemmas -/

/-
The ℓ¹ norm of a vector in the L∞ ball of radius `r` is at most `d * r`.
-/

/-
Each score changes by at most `K * d * r` under an L∞ perturbation of radius `r`.
-/

/-
The pairwise margin drops by at most `2 * K * d * r` under perturbation.
-/

/-! ## Main theorems -/

/-
If the pairwise margin between classes `i` and `j` exceeds `2 * K * d * r`,
    then the pairwise preference is preserved under any L∞ perturbation of radius `r`.
-/

/-
**Condorcet robustness theorem.** If class `c` beats every other class by a margin
    exceeding `2 * K * d * r`, then `c` remains a Condorcet winner after any L∞
    perturbation of radius `r`.
-/

/-
**Smith singleton robustness.** Under uniform margin domination, the singleton
    Smith set `{c}` is preserved after perturbation.
-/

/-
**GL3 specialization.** For a 3-class tropical Hecke classifier, uniform pairwise
    margin domination certifies top-cycle robustness.
-/

/-
**Dominance cut preservation.** If every class in `S` beats every class outside `S`
    by a margin exceeding `2 * K * d * r`, then all cross-edges are preserved under
    any L∞ perturbation of radius `r`. This is the key tournament-theoretic invariant
    behind top-cycle stability.
-/


