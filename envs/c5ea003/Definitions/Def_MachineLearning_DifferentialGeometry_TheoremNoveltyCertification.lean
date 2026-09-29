-- Prove2me | Definitions.Def_MachineLearning_DifferentialGeometry_TheoremNoveltyCertification
-- name    : MachineLearning_DifferentialGeometry_TheoremNoveltyCertification
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:42.061255+00:00
-- url     : https://prove2.me/theorems/7d6a5c18-b8aa-4572-ad93-2a67e9a696c4
-- title:
--   Aether Catalog definitions — MachineLearning_DifferentialGeometry_TheoremNoveltyCertification
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.DifferentialGeometry.TheoremNoveltyCertification`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/DifferentialGeometry/TheoremNoveltyCertification.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Certified Novelty Detection via Theorem Embedding Uniqueness

This module formalizes a metric-geometric framework for certifying that a theorem
(represented by a descriptor) is *novel* relative to a finite catalog of known results.

The key idea: if we embed theorem descriptors into a metric space such that
"equivalent" theorems map within distance δ, then any candidate whose embedding
is farther than δ from every catalog point cannot be equivalent to any known theorem.

## Main results

- `novelty_of_far_from_catalog`: Sound novelty certification via metric separation.
- `novelty_of_nearestDist_gt`: Nearest-neighbor novelty score certification.
- `exists_nearest_in_finset`: Existence of a nearest catalog element.
- `not_equivalent_of_coordinate_gap`: Feature-gap obstruction for non-equivalence.
- `nonequiv_of_symbolCount_gap`: Concrete coordinate gap for theorem descriptors.
- `catalog_separation_implies_novelty_or_unique_match`: Partial completeness.
-/


open scoped BigOperators

/-! ## Core Novelty Framework -/

section Novelty

variable {σ α : Type*}
variable [PseudoMetricSpace α]
variable (Equivalent : σ → σ → Prop)
variable (E : σ → α)

/-- A theorem descriptor `x` is *novel* with respect to a catalog `K` and an equivalence
relation if it is not equivalent to any element of the catalog. -/
def Novel (K : Finset σ) (x : σ) : Prop :=
  ∀ a ∈ K, ¬ Equivalent x a

/-
**Sound novelty certification.** If equivalent descriptors embed within distance δ,
then any candidate farther than δ from every catalog element is novel.
-/

/-! ## Nearest-Neighbor Novelty Score -/

/-- The nearest distance from a candidate `x` to the catalog `K`, defined as
the infimum of distances to catalog elements. -/
noncomputable def nearestDist (K : Finset σ) (x : σ) (hK : K.Nonempty) : ℝ :=
  K.inf' hK (fun a => dist (E x) (E a))

/-
**Nearest-neighbor novelty certification.** If the nearest catalog distance exceeds δ,
the candidate is novel.
-/

/-
**Existence of a nearest catalog element.** For any nonempty finite catalog,
there exists an element achieving the minimum distance.
-/

/-
The nearest distance equals the distance to some catalog element.
-/

/-
Every catalog element is at least as far as the nearest distance.
-/

/-! ## Feature-Gap Obstruction -/

/-
**Coordinate-gap non-equivalence.** If a real-valued feature of two descriptors
differs by more than the equivalence tolerance, the descriptors are not equivalent.
-/

/-! ## Concrete Theorem Descriptor -/

/-- A concrete syntactic/structural descriptor for a theorem, capturing
key features that can be extracted from a formal statement. -/
structure TheoremDescriptor where
  /-- Number of free variables / parameters. -/
  arity : ℕ
  /-- Total count of symbols in the statement. -/
  symbolCount : ℕ
  /-- Maximum nesting depth of quantifiers. -/
  quantifierDepth : ℕ
  /-- Number of dependencies (imported lemmas used). -/
  dependencyCount : ℕ
  /-- Whether the proof uses induction. -/
  hasInduction : Bool
  /-- Whether the proof uses contradiction/contrapositive. -/
  hasContradiction : Bool
deriving DecidableEq

/-
**Symbol-count gap implies non-equivalence.**
-/

/-
**Arity gap implies non-equivalence.**
-/

/-
**Quantifier-depth gap implies non-equivalence.**
-/

/-! ## Sound-and-Partially-Complete Certification -/

/-
**Completeness direction.** If the candidate is not far from every catalog element
(i.e., the novelty certification fails), then there exists a catalog element within δ.
-/

/-! ## Nearest Neighbor Uniqueness Under Strict Separation -/

/-
**Equal nearest distances.** If two catalog elements both achieve the minimum
distance to a candidate, they have equal distances.
-/

/-! ## Novelty Score Monotonicity -/

/-
The novelty score is non-negative.
-/

/-
Adding an element to the catalog can only decrease or maintain the novelty score.
-/

/-! ## Multi-Feature Obstruction -/

/-
**Joint feature gap.** If any one of multiple feature extractors witnesses a gap
beyond its tolerance, the descriptors are not equivalent.
-/

end Novelty


