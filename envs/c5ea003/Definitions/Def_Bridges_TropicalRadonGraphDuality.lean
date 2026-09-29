-- Prove2me | Definitions.Def_Bridges_TropicalRadonGraphDuality
-- name    : Bridges_TropicalRadonGraphDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:28:08.516159+00:00
-- url     : https://prove2.me/theorems/5ccef1ce-9534-4d38-9a50-697b0ba639f5
-- title:
--   Aether Catalog definitions — Bridges_TropicalRadonGraphDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalRadonGraphDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalRadonGraphDuality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Radon Transform Duality via Idempotent Sheaf Semimodules
# and Certified Metric-Graph Reconstruction

This file establishes a finite tropical tomography duality: weighted star trees
are reconstructed from idempotent path-integral (distance) data, and the Radon-style
data is characterized intrinsically via tropical metric axioms.

## Main Results

* `tropical_plus_distributes_over_min` — min-plus distributivity
* `starDist_self`, `starDist_symm` — metric axioms
* `starDist_pos` — positive distances for distinct vertices
* `starDist_triangle` — triangle inequality
* `starDist_fourPoint` — four-point condition
* `starDist_isStarMetric` — star metric characterization
* `starDist_determines_weights` — faithfulness (injectivity)
* `reconstructWeights_correct` — certified weight recovery
* `starTree_reconstruction_certified` — full certified inverse
* `minimal_realization_unique` — uniqueness of realization
* `tropicalRadon_star_duality` — main duality theorem package
* `StarTreeMorphism.preserves_dist` — functoriality
* `morphism_faithful` — morphism-level faithfulness

## Keywords

tropical Radon transform, idempotent tomography, metric graph reconstruction,
min-plus integral geometry, tree metric realization, certified reconstruction,
network tomography, phylogenetic reconstruction
-/


open Finset BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace TropicalRadonGraphDuality

/-! ## §1. Tropical Semiring Foundations -/






/-! ## §2. Star Tree Distance Function

Vertices are `Option (Fin n)`: `none` = root, `some i` = leaf i. -/

/-- Edge weights for a star tree with n leaves. -/
structure StarTreeData (n : ℕ) where
  weight : Fin n → ℕ
  weight_pos : ∀ i, 0 < weight i

variable {n : ℕ}

/-- Distance function for a star tree. -/
def starDist (S : StarTreeData n) : Option (Fin n) → Option (Fin n) → ℕ
  | none, none => 0
  | none, some j => S.weight j
  | some i, none => S.weight i
  | some i, some j => if i = j then 0 else S.weight i + S.weight j





theorem starDist_self (S : StarTreeData n) (v : Option (Fin n)) :
    starDist S v v = 0 := by
  cases v with
  | none => rfl
  | some i => simp [starDist]

theorem starDist_symm (S : StarTreeData n) (u v : Option (Fin n)) :
    starDist S u v = starDist S v u := by
  cases u with
  | none => cases v with | none => rfl | some j => rfl
  | some i => cases v with
    | none => rfl
    | some j =>
      simp only [starDist]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]; omega

theorem starDist_pos (S : StarTreeData n) (u v : Option (Fin n)) (huv : u ≠ v) :
    0 < starDist S u v := by
  rcases u with ( _ | i ) <;> rcases v with ( _ | j ) <;> norm_num [ starDist ] at *;
  · exact S.weight_pos j;
  · exact S.weight_pos i;
  · split_ifs ; linarith [ S.weight_pos i, S.weight_pos j ]

theorem starDist_triangle (S : StarTreeData n) (u v w : Option (Fin n)) :
    starDist S u w ≤ starDist S u v + starDist S v w := by
  cases u <;> cases v <;> cases w <;> simp +decide [ starDist ];
  · grind;
  · split_ifs <;> simp +decide [ *, add_comm ];
  · grind;
  · split_ifs <;> simp_all +arith +decide

/-! ## §3. Four-Point Condition -/

def FourPointCondition {α : Type*} (d : α → α → ℕ) : Prop :=
  ∀ x y z w, d x y + d z w ≤ max (d x z + d y w) (d x w + d y z)


/-! ## §4. Star Metric Property -/

def IsStarMetric {α : Type*} (d : α → α → ℕ) (c : α) : Prop :=
  ∀ u v, u ≠ v → u ≠ c → v ≠ c → d u v = d u c + d c v


def Separated {α : Type*} (d : α → α → ℕ) : Prop :=
  ∀ u v, u ≠ v → ∃ w, d u w ≠ d v w


/-! ## §5. Finite Metric Structure -/

structure FiniteMetricOn (α : Type*) where
  dist : α → α → ℕ
  dist_self : ∀ v, dist v v = 0
  dist_symm : ∀ u v, dist u v = dist v u
  dist_triangle : ∀ u v w, dist u w ≤ dist u v + dist v w
  dist_pos : ∀ u v, u ≠ v → 0 < dist u v

def starTreeMetric (S : StarTreeData n) : FiniteMetricOn (Option (Fin n)) where
  dist := starDist S
  dist_self := starDist_self S
  dist_symm := starDist_symm S
  dist_triangle := starDist_triangle S
  dist_pos := starDist_pos S

/-! ## §6. Admissible Radon Data -/

structure AdmissibleRadonStar (n : ℕ) where
  metric : FiniteMetricOn (Option (Fin n))
  star_center : IsStarMetric metric.dist none
  separated : Separated metric.dist
  fourPoint : FourPointCondition metric.dist


/-! ## §7. Tropical Semimodule Operations -/

def tropicalAdd {α : Type*} (d₁ d₂ : α → α → ℕ) : α → α → ℕ :=
  fun i j => min (d₁ i j) (d₂ i j)

def tropicalSmul {α : Type*} (c : ℕ) (d : α → α → ℕ) : α → α → ℕ :=
  fun i j => c + d i j





/-! ## §8. Faithfulness -/

def tropicalRadonData (S : StarTreeData n) :
    Option (Fin n) → Option (Fin n) → ℕ := starDist S



/-! ## §9. Reconstruction -/

def reconstructWeights (d : Option (Fin n) → Option (Fin n) → ℕ) : Fin n → ℕ :=
  fun i => d none (some i)


/-
**Certified reconstruction**: a star metric is realized by the reconstructed tree.
-/

/-! ## §10. Uniqueness -/


/-! ## §11. Main Duality Theorem -/


/-! ## §12. Morphisms -/

structure StarTreeMorphism (S₁ S₂ : StarTreeData n) where
  leafMap : Fin n → Fin n
  injective : Function.Injective leafMap
  weight_eq : ∀ i, S₂.weight (leafMap i) = S₁.weight i

def StarTreeMorphism.vertexMap {S₁ S₂ : StarTreeData n}
    (f : StarTreeMorphism S₁ S₂) : Option (Fin n) → Option (Fin n)
  | none => none
  | some i => some (f.leafMap i)



/-! ## §13. Sheaf Properties -/

def TropicalGluing {α : Type*} (d : α → α → ℕ) : Prop :=
  ∀ u v w, d u w ≤ d u v + d v w



/-! ## §14. Restriction Maps -/

def restrictStarDist (S : StarTreeData n) {k : ℕ} (f : Fin k → Fin n) :
    Option (Fin k) → Option (Fin k) → ℕ
  | none, none => 0
  | none, some j => S.weight (f j)
  | some i, none => S.weight (f i)
  | some i, some j => if i = j then 0 else S.weight (f i) + S.weight (f j)



/-! ## §15. Concrete Examples -/


end TropicalRadonGraphDuality


