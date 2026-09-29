-- Prove2me | Definitions.Def_Bridges_GL3KemenyRobustness
-- name    : Bridges_GL3KemenyRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T09:16:16.328366+00:00
-- url     : https://prove2.me/theorems/d9007b84-a4c6-4ff4-acd2-107246da235c
-- title:
--   Aether Catalog definitions — Bridges_GL3KemenyRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3KemenyRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3KemenyRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL3 Kemeny–Young Certified Robustness

This file formalizes certified robustness for a 3-class decision rule obtained via
Kemeny–Young aggregation. For 3 candidates, the Kemeny score of each of the 6 possible
rankings is an explicit affine-linear form in three pairwise margins. This allows us to
transfer Lipschitz control on individual class scores to a certified robustness radius for
the Kemeny winner.

## Main results

* `margin_perturbation_bound` — pairwise margins perturb by at most `2 * Kd * ε`
* `kemenyScore_perturbation_bound` — each Kemeny score perturbs by at most `6 * Kd * ε`
* `unique_kemeny_winner_stable` — if the gap exceeds `12 * Kd * ε`, the winner is preserved
* `kemeny_winner_certified_radius` — certified radius `Δ / (12 * Kd)` for winner preservation
* `kemeny_winner_label_stable` — the top-class label is preserved within the certified radius
-/


open scoped BigOperators

namespace GL3Kemeny

/-! ## Margins -/

/-- Pairwise margin: difference between score of class `i` and class `j`. -/
def margin {α : Type*} (h : α → Fin 3 → ℝ) (x : α) (i j : Fin 3) : ℝ := h x i - h x j



/-! ## The six rankings of Fin 3 -/

/-- The six possible rankings (permutations) of three candidates. Named by the order
    of preference: `r012` means `0 ≻ 1 ≻ 2`. -/
inductive KemenyRanking : Type
  | r012 | r021 | r102 | r120 | r201 | r210
  deriving DecidableEq, Repr

instance : Fintype KemenyRanking where
  elems := {KemenyRanking.r012, KemenyRanking.r021, KemenyRanking.r102,
            KemenyRanking.r120, KemenyRanking.r201, KemenyRanking.r210}
  complete := by intro x; cases x <;> simp

namespace KemenyRanking

instance : Inhabited KemenyRanking := ⟨r012⟩

/-- The top-ranked class of a ranking. -/
def topClass : KemenyRanking → Fin 3
  | r012 => 0
  | r021 => 0
  | r102 => 1
  | r120 => 1
  | r201 => 2
  | r210 => 2

end KemenyRanking

/-! ## Kemeny scores

The Kemeny score of a ranking `σ` is the sum of `margin h x (σ i) (σ j)` over pairs `i < j`
in the ranking order. For three candidates this is a sum of three signed margins. -/

/-- The Kemeny score of a ranking at point `x` under score map `h`.
    Each score is expressed as a sum of three signed margins. -/
def kemenyScore {α : Type*} (h : α → Fin 3 → ℝ) (x : α) : KemenyRanking → ℝ
  | .r012 =>  (margin h x 0 1) + (margin h x 0 2) + (margin h x 1 2)
  | .r021 =>  (margin h x 0 1) + (margin h x 0 2) - (margin h x 1 2)
  | .r102 => -(margin h x 0 1) + (margin h x 0 2) + (margin h x 1 2)
  | .r120 => -(margin h x 0 1) - (margin h x 0 2) + (margin h x 1 2)
  | .r201 =>  (margin h x 0 1) - (margin h x 0 2) - (margin h x 1 2)
  | .r210 => -(margin h x 0 1) - (margin h x 0 2) - (margin h x 1 2)

/-! ## Perturbation bounds -/

/-
The pairwise margin perturbs by at most `2 * Kd * ε` when each score perturbs by `Kd * ε`.
-/

/-
Each Kemeny score perturbs by at most `6 * Kd * ε`, since each score is a sum of three
    signed margins, each perturbing by at most `2 * Kd * ε`.
-/

/-! ## Unique winner and gap -/

/-- A ranking `s` is the unique Kemeny winner at `x` if it strictly dominates all others. -/
def isUniqueKemenyWinner {α : Type*} (h : α → Fin 3 → ℝ) (x : α) (s : KemenyRanking) : Prop :=
  ∀ t, t ≠ s → kemenyScore h x t < kemenyScore h x s

/-! ## Score gap perturbation -/

/-
The gap between any two Kemeny scores perturbs by at most `12 * Kd * ε`.
-/

/-! ## Main stability theorem -/

/-
**Kemeny winner stability**: If the unique Kemeny winner at `x` has a score gap `Δ` over
    all competitors, and each class score perturbs by at most `Kd * ε` with
    `12 * Kd * ε < Δ`, then the same ranking remains the unique winner at `y`.
-/

/-! ## Certified radius corollary -/

/-
**Certified radius**: If `ε < Δ / (12 * Kd)`, the unique Kemeny winner is preserved.
-/

/-! ## Winner label -/

/-- The Kemeny winner class: class `c` is the Kemeny winner if there exists a unique
    optimal ranking whose top element is `c`. -/
def kemenyWinner {α : Type*} (h : α → Fin 3 → ℝ) (x : α) (c : Fin 3) : Prop :=
  ∃ s, KemenyRanking.topClass s = c ∧ isUniqueKemenyWinner h x s

/-
**Label stability**: Under the certified radius, the Kemeny winner label is preserved.
-/

/-! ## Winner region characterization

For each ranking, we can characterize when it has the highest Kemeny score
in terms of explicit linear inequalities on the margins. -/

/-
Ranking `0 ≻ 1 ≻ 2` is the unique Kemeny winner iff all three basic margins are positive.
-/

end GL3Kemeny


