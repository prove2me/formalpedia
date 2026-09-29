-- Prove2me | solution 1 for BoundaryEntropySemimodule.separated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:38:16.474631+00:00
-- url     : https://prove2.me/submissions/ae5923af-02b0-4a42-889d-ac8a4ea4285f

-- Sol generated from Bridges/UltrametricHolographicRenormalization.lean
import Mathlib
import Definitions.Def_Bridges_UltrametricHolographicRenormalization

/-!
# Ultrametric Holographic Renormalization:
# Finite Duality via Prime-Congruence Entropy Semimodules

This file formalizes a finite algebraic theory of **ultrametric holographic reconstruction**:
the principle that hierarchical "bulk" structure is canonically and uniquely recoverable
from "boundary" observable data in finite ultrametric spaces.

## Mathematical Context

The central theorem is a finite, non-Archimedean analogue of holographic reconstruction.
In the holographic principle from theoretical physics, a bulk (higher-dimensional)
spacetime is encoded by data on its lower-dimensional boundary. Here, the "bulk" is a
finite ultrametric hierarchy (conceptually a rooted weighted tree), and the "boundary"
is the entropy profile data observed at the hierarchy's leaves.

This formalizes and extends the reconstruction paradigm from
`reconstructs_bulk_from_boundary_profiles` (CausalHolography.lean), replacing
closure-based observables with **ultrametric entropy profiles** and establishing
a new finite duality theorem in the non-Archimedean regime.

## Main Results

### Core Ultrametric Theory (§1-§2)
* `FiniteUltrametric.entropyProfile_injective` — Boundary entropy profiles separate points
* `FiniteUltrametric.ultra_eq_of_gt` — The ultrametric isosceles lemma
* `FiniteUltrametric.scaleCluster_eq_of_mem` — Scale clusters form equivalence classes
* `FiniteUltrametric.scaleCluster_zero` — Scale-zero clusters are singletons
* `FiniteUltrametric.scaleCluster_disjoint_or_eq` — Clusters partition at each scale

### Boundary Entropy Semimodule (§3)
* `BoundaryEntropySemimodule.separated` — Every semimodule satisfies the separation axiom
* `BoundaryEntropySemimodule.nondegenerate` — Positive definiteness implies nondegeneracy
* `BoundaryEntropySemimodule.roundtrip` — Boundary ↔ Ultrametric bijective correspondence

### Holographic Reconstruction Theorems (§5-§6)
* `boundary_determines_minimal_bulk` — Equal boundary data ⟹ isomorphic minimal bulks
* `exists_unique_minimal_realization` — Existence + uniqueness of minimal realization
* `boundary_complete_on_minimal` — Iso ↔ equal boundary (faithfulness + conservativity)
* `reconstruction_certified` — Canonical reconstruction is provably correct

## Cross-Domain Connections

- **Ultrametric geometry ↔ Hierarchical clustering**: clusters form nested partitions
- **Idempotent algebra ↔ Tropical geometry**: max operation is the join
- **Holographic principle ↔ Realization theory**: boundary determines bulk (Myhill-Nerode)
- **Renormalization flow ↔ Scale-indexed partition refinement**: coarser = more loss
- **Phylogenetics ↔ Dendrogram recovery**: ultrametric tree = clustering tree

## References

- Structural ancestor: `Catalog/Bridges/54bd922e_aristotle/Bridges/CausalHolography.lean`
  (`reconstructs_bulk_from_boundary_profiles`)
- Related: `Catalog/Speculative/AutoResearch/Bridges/UltrametricProofLearning.lean`
  (ultrametric contraction and diagonal stability)
-/

open Finset Function

noncomputable section

universe u

/-! ## §1. Finite Ultrametric Spaces

A finite ultrametric space is a finite set equipped with a ℕ-valued distance function
satisfying the strong triangle inequality `d(x,z) ≤ max(d(x,y), d(y,z))`.
The use of ℕ-valued distances ensures finiteness, decidability, and computability. -/


open FiniteUltrametric

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
Distinct points have positive distance.
-/


/-
**Separation Theorem**: Entropy profiles are injective — distinct points
    have distinct profiles. This is the foundational holographic property.
-/

/-
**Ultrametric Isosceles Lemma**: If `d(x,z) < d(x,y)`, then `d(y,z) = d(x,y)`.
    Every ultrametric triangle is isosceles with the odd side shortest.
-/


/-
Entropy shift dominates pairwise distance (ultrametric triangle).
-/


/-! ## §2. Scale Clusters and Hierarchical Structure

Scale clusters are the building blocks of the bulk hierarchy. At each scale s,
the cluster of x consists of all points within distance ≤ s. The ultrametric
axiom ensures these clusters form equivalence classes — a chain of nested
partitions that gives the hierarchy its tree structure. -/

open FiniteUltrametric

variable {α : Type*} [DecidableEq α] [Fintype α]


/-
Every point is in its own cluster.
-/

/-
Clusters grow with scale.
-/

/-
**Cluster Equivalence**: If y is in x's cluster at scale s, their clusters
    coincide. This is the key ultrametric property: at each scale, clusters
    either coincide or are disjoint, yielding a partition.
-/

/-
At scale 0, clusters are singletons — maximum resolution.
-/

/-
Clusters are either disjoint or identical (ultrametric partition property).
-/


/-! ## §3. Boundary Entropy Semimodule

The boundary entropy semimodule encodes observable data at the boundary of an
ultrametric hierarchy. It is the "dual object" to the bulk: the bulk determines
it, and under separation and nondegeneracy it determines the bulk back.

Mathematically, a `BoundaryEntropySemimodule` is equivalent to a `FiniteUltrametric`.
The conceptual distinction is that it represents the *observer-facing* data. -/


open BoundaryEntropySemimodule

variable {α : Type*} [DecidableEq α] [Fintype α]



/-
Boundary ↔ Ultrametric roundtrip (direction 1).
-/

/-
Boundary ↔ Ultrametric roundtrip (direction 2).
-/


/-
Every boundary entropy semimodule is separated (by positive definiteness).
-/


/-
Every boundary entropy semimodule is nondegenerate.
-/




/-
Equivalence coincides with structural equality.
-/


/-! ## §4. Ultrametric Bulk Flow

The bulk flow is the "hidden" ultrametric structure extending the boundary observer
space. Internal nodes represent hierarchical merge points; boundary observers are
embedded as leaves. -/


attribute [instance] UltrametricBulkFlow.instDecEqNode UltrametricBulkFlow.instFintypeNode

open UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]




/-
In a minimal bulk flow, node profiles are injective.
    Every node is uniquely identified by its boundary signature.
-/


/-
The canonical bulk flow is minimal.
-/

/-
The canonical bulk flow realizes the original boundary data.
-/



/-! ## §5. Holographic Reconstruction Theorems

The core duality: boundary entropy data determines minimal bulk structure,
uniquely up to isomorphism. -/

open UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
**Holographic Faithfulness**: Equal boundary data on minimal bulk flows
    implies isomorphism. Boundary observables completely determine the bulk.
    This generalizes `reconstructs_bulk_from_boundary_profiles` from
    CausalHolography.lean to the ultrametric/entropy regime.
-/

/-
Isomorphic minimal bulk flows have equal boundary data (converse direction).
-/

/-
**Boundary Completeness**: For minimal bulk flows, isomorphism ↔ equal boundary.
    The boundary functor is faithful and conservative on minimal objects.
-/

/-
**Existence**: Every boundary semimodule has a minimal bulk realization.
-/

/-
**Existence and Uniqueness**: The minimal realization is unique up to iso.
    This is the complete holographic duality theorem — a bijective correspondence
    between boundary entropy semimodules and isomorphism classes of minimal
    ultrametric bulk flows. Analogous to the Myhill-Nerode theorem for automata
    and the Hankel matrix minimal realization theorem from systems theory.
-/

/-
Variant with explicit separation, nondegeneracy, and finite generation hypotheses.
-/


/-! ## §6. Certified Reconstruction

The holographic reconstruction is not just an existence theorem — it provides an
explicit certified construction. -/

open UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]




/-
**Certified Correctness**: For any minimal bulk flow U, reconstructing from
    its boundary yields a bulk flow isomorphic to U.
-/

/-
Full roundtrip: reconstruct ∘ boundary ≅ id on minimal bulk flows.
-/


/-! ## §7. Additional Properties -/

open UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]





open BoundaryEntropySemimodule in
theorem solution(B : BoundaryEntropySemimodule α) : B.Separated := by
  intro x y hxy
  by_contra h_contra
  push_neg at h_contra
  have h_eq : ∀ z, B.profile x z = B.profile y z := by
    exact h_contra
  have h_eq_self : B.profile x y = B.profile y y := by
    exact h_eq y
  have h_eq_zero : B.profile x y = 0 := by
    rw [ h_eq_self, B.profile_self ]
  have h_eq_x : x = y := by
    exact B.profile_pos x y h_eq_zero
  contradiction
