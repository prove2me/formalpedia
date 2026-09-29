-- Prove2me | Definitions.Def_Bridges_GL3SatakeAbstainRobustness
-- name    : Bridges_GL3SatakeAbstainRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:43.157384+00:00
-- url     : https://prove2.me/theorems/76afad7d-80ed-4c81-bd24-8803825142a8
-- title:
--   Aether Catalog definitions — Bridges_GL3SatakeAbstainRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GL3SatakeAbstainRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GL3SatakeAbstainRobustness.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# GL₃ Tropical Satake Abstain Robustness

This file formalizes a selective multiclass classifier with reject option for three
tropical Satake/Hecke scores and proves stability theorems for both the accept and
reject decisions under perturbation, given pairwise-difference Lipschitz bounds on
the score functions.

## Main results

* `abstain_classifier_some_of_margin_ball` — robust preservation of a non-abstaining
  class decision from a strict top-2 margin bound.
* `abstain_classifier_none_of_topMargin_ball` — robust preservation of abstention
  from a strict top margin bound.
* `abstain_classifier_eq_some_preserved` — classifier-level preservation of `some i`.
* `abstain_classifier_none_preserved_half_radius` — half-radius corollary for
  abstention preservation matching the existing robustness library style.

## Design notes

The uniqueness lemma `classMargin_gt_tau_unique` and the classifier-level iff
`abstainClassifier_some_iff` require `0 ≤ τ`. This is because for negative `τ`,
multiple classes can simultaneously have margin above `τ` (e.g., when two classes
are tied for the top score). With `0 ≤ τ`, the margin condition forces a strict
argmax, which is unique.

The core robustness results (`abstain_classifier_some_of_margin_ball` and
`abstain_classifier_none_of_topMargin_ball`) do NOT require `0 ≤ τ` — they work
purely at the scalar margin level.
-/


open Finset

noncomputable section

/-! ## Definitions -/

/-- Score vector: three real-valued score functions on a type `X`. -/
def ScoreVec (X : Type*) := Fin 3 → X → ℝ

private lemma erase_nonempty (i : Fin 3) :
    ((Finset.univ : Finset (Fin 3)).erase i).Nonempty := by
  fin_cases i
  · exact ⟨(1 : Fin 3), Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩⟩
  · exact ⟨(0 : Fin 3), Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩⟩
  · exact ⟨(0 : Fin 3), Finset.mem_erase.mpr ⟨by decide, Finset.mem_univ _⟩⟩

/-- The maximum score among competitors of class `i`. -/
def otherMax {X : Type*} (s : Fin 3 → X → ℝ) (i : Fin 3) (x : X) : ℝ :=
  ((Finset.univ.erase i).sup' (erase_nonempty i) (fun j => s j x))

/-- The margin of class `i`: score of `i` minus the maximum competing score. -/
def classMargin {X : Type*} (s : Fin 3 → X → ℝ) (i : Fin 3) (x : X) : ℝ :=
  s i x - otherMax s i x

/-- Selective classifier with abstention. Returns `some i` if class `i` has
    margin strictly above `τ`, and `none` (abstain) otherwise. -/
def abstainClassifier {X : Type*}
    (s : Fin 3 → X → ℝ) (τ : ℝ) (x : X) : Option (Fin 3) :=
  if h : ∃ i : Fin 3, τ < classMargin s i x then
    some (Classical.choose h)
  else
    none

/-- The top margin across all classes. -/
def topMargin {X : Type*} (s : Fin 3 → X → ℝ) (x : X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => classMargin s i x)

/-- Pairwise score differences are `Kd`-Lipschitz. -/
def PairwiseDiffLipschitz {X : Type*} [PseudoMetricSpace X]
    (s : Fin 3 → X → ℝ) (Kd : ℝ) : Prop :=
  ∀ i j : Fin 3, ∀ x y : X,
    |(s i x - s j x) - (s i y - s j y)| ≤ Kd * dist x y

/-! ## Uniqueness of the winning class -/

/-
If two classes both have margin strictly above a nonneg threshold `τ`,
    they must be the same class. With `0 ≤ τ`, the margin condition forces
    `s i x` to be strictly larger than all other scores, giving uniqueness.
-/

/-! ## Characterization lemmas -/

/-
`classMargin` equals the infimum of pairwise differences over competitors.
-/

/-
Threshold is below class margin iff it is below all pairwise differences
    with competitors.
-/

/-
The abstain classifier returns `some i` iff class `i` has margin above `τ`.
    Requires `0 ≤ τ` for uniqueness of the winning class.
-/

/-
The abstain classifier returns `none` iff all class margins are at most `τ`.
-/

/-! ## Lipschitz bounds -/

/-
Class margin is `Kd`-Lipschitz under pairwise-difference Lipschitz scores.
-/

/-
Top margin is `Kd`-Lipschitz under pairwise-difference Lipschitz scores.
-/

/-! ## Core scalar threshold robustness -/



/-! ## Main robustness theorems -/



/-
**Half-radius corollary for non-abstention preservation**.
-/

/-
**Sharp abstention robustness**: if top margin is below `τ` at `x`,
    then the classifier abstains at any `y` within the certified radius.
-/

/-
**Half-radius corollary for abstention preservation**.
-/

end


