-- Prove2me | Definitions.Def_Bridges_UltrametricHolographicRenormalization
-- name    : Bridges_UltrametricHolographicRenormalization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:21.732332+00:00
-- url     : https://prove2.me/theorems/2501b721-806a-45c4-8aba-f4b110b5ac5b
-- title:
--   Aether Catalog definitions — Bridges_UltrametricHolographicRenormalization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricHolographicRenormalization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricHolographicRenormalization.lean by skeleton subtraction
import Mathlib

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

/-- A finite ultrametric space with ℕ-valued distance.
    The strong triangle inequality makes every triangle isosceles with the
    unequal side (if any) being the shortest. -/
@[ext]
structure FiniteUltrametric (α : Type*) where
  dist : α → α → ℕ
  dist_self : ∀ x, dist x x = 0
  dist_comm : ∀ x y, dist x y = dist y x
  dist_eq_zero : ∀ x y, dist x y = 0 → x = y
  dist_ultra : ∀ x y z, dist x z ≤ max (dist x y) (dist y z)

namespace FiniteUltrametric

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
Distinct points have positive distance.
-/

/-- The entropy profile of a point: its distance vector to all other points.
    This is the fundamental "boundary observable" — what an observer at x measures. -/
def entropyProfile (U : FiniteUltrametric α) (x : α) : α → ℕ :=
  U.dist x

/-
**Separation Theorem**: Entropy profiles are injective — distinct points
    have distinct profiles. This is the foundational holographic property.
-/

/-
**Ultrametric Isosceles Lemma**: If `d(x,z) < d(x,y)`, then `d(y,z) = d(x,y)`.
    Every ultrametric triangle is isosceles with the odd side shortest.
-/

/-- The entropy shift: max of distances from z to x and y.
    This is the "shifted entropy" in the boundary semimodule. -/
def entropyShift (U : FiniteUltrametric α) (x y z : α) : ℕ :=
  max (U.dist x z) (U.dist y z)

/-
Entropy shift dominates pairwise distance (ultrametric triangle).
-/

end FiniteUltrametric

/-! ## §2. Scale Clusters and Hierarchical Structure

Scale clusters are the building blocks of the bulk hierarchy. At each scale s,
the cluster of x consists of all points within distance ≤ s. The ultrametric
axiom ensures these clusters form equivalence classes — a chain of nested
partitions that gives the hierarchy its tree structure. -/

namespace FiniteUltrametric

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The cluster of x at scale s: all points within distance ≤ s. -/
def scaleCluster (U : FiniteUltrametric α) (s : ℕ) (x : α) : Finset α :=
  Finset.univ.filter (fun y => U.dist x y ≤ s)

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

end FiniteUltrametric

/-! ## §3. Boundary Entropy Semimodule

The boundary entropy semimodule encodes observable data at the boundary of an
ultrametric hierarchy. It is the "dual object" to the bulk: the bulk determines
it, and under separation and nondegeneracy it determines the bulk back.

Mathematically, a `BoundaryEntropySemimodule` is equivalent to a `FiniteUltrametric`.
The conceptual distinction is that it represents the *observer-facing* data. -/

/-- Boundary entropy semimodule: the observable entropy profile data.
    The join operation (max) is idempotent, giving tropical/max-plus structure. -/
@[ext]
structure BoundaryEntropySemimodule (α : Type*) where
  profile : α → α → ℕ
  profile_comm : ∀ x y, profile x y = profile y x
  profile_self : ∀ x, profile x x = 0
  profile_pos : ∀ x y, profile x y = 0 → x = y
  profile_ultra : ∀ x y z, profile x z ≤ max (profile x y) (profile y z)

namespace BoundaryEntropySemimodule

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Extract boundary semimodule from a finite ultrametric. -/
def ofUltrametric (U : FiniteUltrametric α) : BoundaryEntropySemimodule α where
  profile := U.dist
  profile_comm := U.dist_comm
  profile_self := U.dist_self
  profile_pos := U.dist_eq_zero
  profile_ultra := U.dist_ultra

/-- Convert boundary semimodule back to a finite ultrametric. -/
def toUltrametric (B : BoundaryEntropySemimodule α) : FiniteUltrametric α where
  dist := B.profile
  dist_self := B.profile_self
  dist_comm := B.profile_comm
  dist_eq_zero := B.profile_pos
  dist_ultra := B.profile_ultra

/-
Boundary ↔ Ultrametric roundtrip (direction 1).
-/

/-
Boundary ↔ Ultrametric roundtrip (direction 2).
-/

/-- **Separation**: Distinct observers have distinct entropy profiles.
    The observability condition for holographic reconstruction. -/
def Separated (B : BoundaryEntropySemimodule α) : Prop :=
  ∀ x y : α, x ≠ y → ∃ z : α, B.profile x z ≠ B.profile y z

/-
Every boundary entropy semimodule is separated (by positive definiteness).
-/

/-- **Nondegeneracy**: Distinct observers have positive entropy distance. -/
def Nondegenerate (B : BoundaryEntropySemimodule α) : Prop :=
  ∀ x y : α, x ≠ y → 0 < B.profile x y

/-
Every boundary entropy semimodule is nondegenerate.
-/

/-- Finite generation (trivially true for finite types). -/
def FinitelyGenerated (_B : BoundaryEntropySemimodule α) : Prop := True


/-- Equivalence: profile equality. -/
def Equivalent (B₁ B₂ : BoundaryEntropySemimodule α) : Prop :=
  B₁.profile = B₂.profile

/-
Equivalence coincides with structural equality.
-/

end BoundaryEntropySemimodule

/-! ## §4. Ultrametric Bulk Flow

The bulk flow is the "hidden" ultrametric structure extending the boundary observer
space. Internal nodes represent hierarchical merge points; boundary observers are
embedded as leaves. -/

/-- An ultrametric bulk flow: a finite ultrametric space containing the boundary
    observers as an embedded subspace. The boundary restriction gives the
    observable entropy data. -/
structure UltrametricBulkFlow (α : Type u) [DecidableEq α] [Fintype α] where
  Node : Type u
  instDecEqNode : DecidableEq Node
  instFintypeNode : Fintype Node
  embed : α ↪ Node
  scaleDist : Node → Node → ℕ
  scaleDist_self : ∀ n, scaleDist n n = 0
  scaleDist_comm : ∀ m n, scaleDist m n = scaleDist n m
  scaleDist_pos : ∀ m n, scaleDist m n = 0 → m = n
  scaleDist_ultra : ∀ x y z, scaleDist x z ≤ max (scaleDist x y) (scaleDist y z)

attribute [instance] UltrametricBulkFlow.instDecEqNode UltrametricBulkFlow.instFintypeNode

namespace UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The boundary restriction: extract boundary entropy data from a bulk flow.
    This is the "holographic projection." -/
def boundary (U : UltrametricBulkFlow α) : BoundaryEntropySemimodule α where
  profile := fun a b => U.scaleDist (U.embed a) (U.embed b)
  profile_comm := fun _ _ => U.scaleDist_comm _ _
  profile_self := fun _ => U.scaleDist_self _
  profile_pos := fun _ _ h => U.embed.injective (U.scaleDist_pos _ _ h)
  profile_ultra := fun _ _ _ => U.scaleDist_ultra _ _ _

/-- **Minimality**: A bulk flow is minimal if its embedding is surjective —
    every node is a boundary observer, with no superfluous internal structure.
    This is the finite analogue of "minimal realization" from systems theory. -/
def Minimal (U : UltrametricBulkFlow α) : Prop :=
  Surjective U.embed

/-- The boundary profile of a node: its distance to all boundary observers.
    This is the "holographic signature" — how a node appears from the boundary. -/
def nodeProfile (U : UltrametricBulkFlow α) (n : U.Node) : α → ℕ :=
  fun a => U.scaleDist (U.embed a) n

/-
In a minimal bulk flow, node profiles are injective.
    Every node is uniquely identified by its boundary signature.
-/

/-- The canonical bulk flow from boundary data: Node = α, embed = id.
    This is the explicit "holographic decoder." -/
def canonical (B : BoundaryEntropySemimodule α) : UltrametricBulkFlow α where
  Node := α
  instDecEqNode := inferInstance
  instFintypeNode := inferInstance
  embed := ⟨id, fun _ _ h => h⟩
  scaleDist := B.profile
  scaleDist_self := B.profile_self
  scaleDist_comm := B.profile_comm
  scaleDist_pos := B.profile_pos
  scaleDist_ultra := B.profile_ultra

/-
The canonical bulk flow is minimal.
-/

/-
The canonical bulk flow realizes the original boundary data.
-/

/-- Isomorphism of bulk flows: a distance-preserving bijection that
    respects the boundary embedding. -/
structure Iso (U V : UltrametricBulkFlow α) where
  toEquiv : U.Node ≃ V.Node
  preserves_embed : ∀ a, toEquiv (U.embed a) = V.embed a
  preserves_dist : ∀ m n, V.scaleDist (toEquiv m) (toEquiv n) = U.scaleDist m n

end UltrametricBulkFlow

/-! ## §5. Holographic Reconstruction Theorems

The core duality: boundary entropy data determines minimal bulk structure,
uniquely up to isomorphism. -/

namespace UltrametricBulkFlow

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

end UltrametricBulkFlow

/-! ## §6. Certified Reconstruction

The holographic reconstruction is not just an existence theorem — it provides an
explicit certified construction. -/

namespace UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- **Certified Reconstruction**: Build a bulk flow from boundary data. -/
def reconstructFromBoundary (B : BoundaryEntropySemimodule α) :
    UltrametricBulkFlow α :=
  canonical B



/-
**Certified Correctness**: For any minimal bulk flow U, reconstructing from
    its boundary yields a bulk flow isomorphic to U.
-/

/-
Full roundtrip: reconstruct ∘ boundary ≅ id on minimal bulk flows.
-/

end UltrametricBulkFlow

/-! ## §7. Additional Properties -/

namespace UltrametricBulkFlow

variable {α : Type*} [DecidableEq α] [Fintype α]




end UltrametricBulkFlow


