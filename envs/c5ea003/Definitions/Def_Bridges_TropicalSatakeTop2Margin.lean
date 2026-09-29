-- Prove2me | Definitions.Def_Bridges_TropicalSatakeTop2Margin
-- name    : Bridges_TropicalSatakeTop2Margin
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:43:09.522748+00:00
-- url     : https://prove2.me/theorems/246dc970-a6e3-4384-b471-cf2383346b21
-- title:
--   Aether Catalog definitions — Bridges_TropicalSatakeTop2Margin
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalSatakeTop2Margin`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalSatakeTop2Margin.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Satake Top-2 Margin Theorem for GL₃ Hecke Score Classifiers

This file formalizes a sharp robustness theorem for top-2 label sets determined by
score triples `x : Fin 3 → ℝ`. The key results are:

1. **Unique top-2 set characterization**: A unique top-2 set exists iff there is a unique
   "bottom" class strictly below the other two.

2. **Perturbation stability**: If the minimum gap from the excluded class to the top-2 set
   exceeds `2ε`, then any coordinatewise `ε`-perturbation preserves the top-2 set.

3. **Sharp converse**: If one member of the top-2 set has margin at most `2ε` over the
   excluded class, then there exists an `ε`-perturbation destroying the top-2 set.

4. **Max-plus transfer**: For max-plus linear score models (tropical Satake reconstructions),
   test-family perturbation of size `η` induces score perturbation of size at most `η`,
   giving a concrete robustness certificate.

## Mathematical context

For GL₃ tropical Satake classifiers, scores are computed as max-plus linear forms on
a finite test family. The top-2 label set identifies the two most plausible classes.
Robustness of this label set under perturbation of the test valuations is the key
certification property. The sharp threshold is governed by the gap between the second
and third ordered scores—equivalently, the minimum separation between the excluded
class and the top-2 pair.
-/

open Finset

namespace TropicalSatake

/-! ## Core definitions -/

/-- A set `A ⊆ Fin 3` is a top-2 set for score vector `x` if it has cardinality 2
and every member of `A` scores strictly above every non-member. -/
def IsTop2Set (x : Fin 3 → ℝ) (A : Finset (Fin 3)) : Prop :=
  A.card = 2 ∧ ∀ i ∈ A, ∀ j ∉ A, x j < x i

/-- Top-2 stability under score perturbation: there exists a top-2 set for `x` that
remains a top-2 set for every `y` within coordinatewise distance `ε`. -/
def Top2StableUnderScorePerturbation (x : Fin 3 → ℝ) (ε : ℝ) : Prop :=
  ∃ A : Finset (Fin 3), IsTop2Set x A ∧
    ∀ y : Fin 3 → ℝ, (∀ i, |y i - x i| ≤ ε) → IsTop2Set y A

/-! ## Finite enumeration helpers for Fin 3 -/


/-
Any two-element subset of `Fin 3` has a unique complement element.
-/

/-! ## Section 1: Unique top-2 set characterization -/

/-
A unique top-2 set exists iff there is a unique bottom class strictly below
all others. This is the cleanest characterization for `Fin 3`.
-/

/-
Equivalent formulation: a unique top-2 set exists iff there is a class `c`
with positive margin to all other classes.
-/

/-! ## Section 2: Top-2 stability under coordinatewise perturbation -/

/-
Key inequality lemma: if `2ε < x a - x c` and both coordinates are perturbed
by at most `ε`, then `y c < y a`.
-/

/-
**Sharp sufficient condition for top-2 stability.**
If the minimum margin from the excluded class to each member of the top-2 set
exceeds `2ε`, then the top-2 set is stable under `ε`-perturbations.
-/

/-
**Sharp converse: existence of a counterperturbation.**
If one member of a top-2 set has margin at most `2ε` over the excluded class,
there exists an `ε`-perturbation destroying the top-2 property.
-/

/-! ## Section 3: Finite test-family score model and Lipschitz transfer -/

/-- A finite test-family score model: scores for 3 classes are computed from
test valuations `v : ℕ → ℝ`, with a Lipschitz bound `K` relating
test-valuation drift to score drift. -/
structure FiniteTestScoreModel where
  /-- The finite set of test indices -/
  T : Finset ℕ
  /-- Score function: given a class and test valuations, produces a score -/
  score : Fin 3 → (ℕ → ℝ) → ℝ
  /-- Lipschitz constant -/
  K : ℝ
  /-- Lipschitz constant is non-negative -/
  K_nonneg : 0 ≤ K
  /-- Lipschitz property: coordinatewise bounded test drift implies bounded score drift -/
  lipschitz : ∀ v w : ℕ → ℝ, ∀ η : ℝ, 0 ≤ η →
    (∀ t ∈ T, |v t - w t| ≤ η) →
    ∀ i : Fin 3, |score i v - score i w| ≤ K * η

/-- The score vector induced by a test valuation. -/
def modelScores (M : FiniteTestScoreModel) (v : ℕ → ℝ) : Fin 3 → ℝ :=
  fun i => M.score i v

/-
**Lipschitz transfer theorem**: if the score margin exceeds `2 * K * η`,
then the top-2 set is preserved under any `η`-perturbation of test valuations.
-/

/-! ## Section 4: Max-plus linear score model -/

/-- Auxiliary: max-plus scores are well-defined when weight sets are nonempty. -/
lemma maxPlusScore_image_nonempty
    (W : Fin 3 → Finset (ℕ × ℝ)) (hne : ∀ i, (W i).Nonempty)
    (v : ℕ → ℝ) (i : Fin 3) :
    ((W i).image (fun p => v p.1 + p.2)).Nonempty :=
  Finset.Nonempty.image (hne i) _

/-- Max-plus score for class `i`: the maximum of `v t + w` over all `(t, w) ∈ W i`.
This is the tropical analogue of a linear score function.
Requires each weight set to be nonempty. -/
noncomputable def MaxPlusScore'
    (W : Fin 3 → Finset (ℕ × ℝ)) (hne : ∀ i, (W i).Nonempty)
    (v : ℕ → ℝ) : Fin 3 → ℝ :=
  fun i => ((W i).image (fun p => v p.1 + p.2)).max'
    (maxPlusScore_image_nonempty W hne v i)

/-
**Max-plus 1-Lipschitz property**: if every test valuation changes by at most `η`,
then every max-plus score changes by at most `η`.
-/

/-
**Max-plus top-2 robustness corollary**: for max-plus score models with test-family
perturbation bounded by `η`, if the margin exceeds `2η` then the top-2 set is stable.
-/

end TropicalSatake


