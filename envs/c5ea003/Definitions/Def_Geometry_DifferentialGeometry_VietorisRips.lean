-- Prove2me | Definitions.Def_Geometry_DifferentialGeometry_VietorisRips
-- name    : Geometry_DifferentialGeometry_VietorisRips
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:03:52.410793+00:00
-- url     : https://prove2.me/theorems/3339f3ee-46c9-4a70-8510-930263292294
-- title:
--   Aether Catalog definitions — Geometry_DifferentialGeometry_VietorisRips
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.DifferentialGeometry.VietorisRips`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/DifferentialGeometry/VietorisRips.lean by skeleton subtraction
import Mathlib
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Vietoris–Rips filtration skeleton

This file formalizes the first verified layer of a persistent homology /
Vietoris–Rips pipeline for finite (pseudo)metric spaces.

We work over a type `α` with `[PseudoMetricSpace α]`.  A *Vietoris–Rips simplex*
at scale `r` is a finite subset all of whose pairwise distances are bounded by
`r`.  We record the basic monotonicity, downward-closure and existence
properties, package the simplices at a fixed scale as a subtype, and define the
canonical scale-inclusion maps together with their functoriality
(identity and composition) laws.

This is intended as a foundation for later formalization of filtered simplicial
complexes and persistent homology.
-/

/-- A Vietoris–Rips simplex at scale `r` is a finite subset whose pairwise
distances are all bounded by `r`. -/
def VRSimplex {α : Type*} [PseudoMetricSpace α] (r : ℝ) (σ : Finset α) : Prop :=
  ∀ x ∈ σ, ∀ y ∈ σ, dist x y ≤ r

/-- Vietoris–Rips simplices are monotone in the scale parameter. -/
theorem VRSimplex_mono {α : Type*} [PseudoMetricSpace α]
    {r s : ℝ} (hrs : r ≤ s) {σ : Finset α} :
    VRSimplex r σ → VRSimplex s σ := by
  intro h x hx y hy
  exact le_trans (h x hx y hy) hrs




/-- The collection of Vietoris–Rips simplices at scale `r`, packaged as a
subtype of `Finset α`. -/
def VRSimplices (α : Type*) [PseudoMetricSpace α] (r : ℝ) :=
  {σ : Finset α // VRSimplex r σ}

/-- The canonical inclusion of VR simplices induced by an inequality `r ≤ s`. -/
def scaleInclusion {α : Type*} [PseudoMetricSpace α]
    {r s : ℝ} (hrs : r ≤ s) :
    VRSimplices α r → VRSimplices α s :=
  fun σ => ⟨σ.1, VRSimplex_mono hrs σ.2⟩


