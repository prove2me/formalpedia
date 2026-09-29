-- Prove2me | Definitions.Def_Geometry_PosetTheory_VietorisRipsThreshold
-- name    : Geometry_PosetTheory_VietorisRipsThreshold
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:49.149828+00:00
-- url     : https://prove2.me/theorems/9573fa09-9106-45fc-bcf8-74e3f6278ac0
-- title:
--   Aether Catalog definitions — Geometry_PosetTheory_VietorisRipsThreshold
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PosetTheory.VietorisRipsThreshold`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PosetTheory/VietorisRipsThreshold.lean by skeleton subtraction
import Mathlib

/-!
# Vietoris–Rips completion threshold

This file formalizes the *completion threshold* for the Vietoris–Rips complex of a
(pseudo)metric space.

We use a lightweight, custom notion of a downward-closed family of finite subsets
(`SimpleComplex`) rather than Mathlib's abstract simplicial complexes, in order to keep
the development self-contained and the proofs robust.

## Main definitions

* `SimpleComplex α` : a set of finite subsets ("faces") closed under taking subsets.
* `fullComplex α`   : the complex whose faces are *all* finite subsets of `α`.
* `vietorisRips ε`  : the Vietoris–Rips complex at scale `ε`; a finite subset is a face
  iff all pairwise distances of its vertices are `≤ ε`.

## Main results

* `mem_fullComplex` / `mem_vietorisRips_iff` : membership characterizations.
* `vietorisRips_eq_fullComplex_iff` :
  `vietorisRips ε = fullComplex α ↔ ∀ x y, dist x y ≤ ε`.
* `vietorisRips_eq_fullComplex_iff_sup'_le` : the finite "maximum pairwise distance"
  packaging of the above when `α` is a finite, nonempty type.
-/

namespace VietorisRipsThreshold

/-- A lightweight simplicial-complex–like structure: a family of finite subsets
("faces") of `α` that is closed under taking subsets. -/
@[ext]
structure SimpleComplex (α : Type*) where
  /-- The faces of the complex. -/
  faces : Set (Finset α)
  /-- The face set is downward closed: a subset of a face is a face. -/
  downward_closed : ∀ ⦃s t : Finset α⦄, s ∈ faces → t ⊆ s → t ∈ faces

variable {α : Type*}

/-- The full complex: every finite subset of `α` is a face. -/
def fullComplex (α : Type*) : SimpleComplex α where
  faces := Set.univ
  downward_closed := by intro s t _ _; trivial


variable [PseudoMetricSpace α]

/-- The Vietoris–Rips complex at scale `ε`: a finite subset is a face iff every pair of
its vertices is at distance `≤ ε`. -/
def vietorisRips (ε : ℝ) : SimpleComplex α where
  faces := {s : Finset α | ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ ε}
  downward_closed := by
    intro s t hs hts x hx y hy
    exact hs x (hts hx) y (hts hy)




end VietorisRipsThreshold


