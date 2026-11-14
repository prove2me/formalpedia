-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:40.168457+00:00
-- url     : https://prove2.me/theorems/42c00b92-7a50-442a-af64-f40130510360
-- title:
--   Occurrence hypergraph bundles and conditional bundle counts
-- statement:
--   A hypergraph bundle has a finite family of occurrence edges and a projection to a fixed base vertex type. The projection is injective on each occurrence edge, whose image must belong to the finite base hypergraph. Inclusion closure means that every subedge of an occurrence edge is also present; bundle order is the maximum edge cardinality, with value zero for an empty edge family.
--
--   The bundle supplies edge erasure, restriction to an edge, and the projection-induced bijection between an occurrence edge and its base image. These maps pull arbitrary local base weights back to occurrence edges. Unit-interval predicates are available for both base and occurrence weights.
--
--   Its product multiplies all occurrence-edge factors at a full assignment, and its count is their normalized mean when the assignment spaces are finite. For a selected edge, the remaining definitions split edge and complementary coordinates, form the remainder product, its conditional average and frozen correlation, and the doubled second moment used by Cauchy–Schwarz.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleCounting.lean#L33-L615

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Hypergraph bundles and the counting-lemma decomposition

Tao's hypergraph counting lemma is proved after passing from one copy of
each vertex class to a *hypergraph bundle*.  A bundle has a finite set of
occurrence vertices, a finite family of occurrence edges, and a projection
to the base vertex classes which is injective on every occurrence edge.
The extra occurrence vertices record the copies created by repeated
Cauchy--Schwarz.

This file supplies the finite bundle object and the exact analytic
identities at one step of the double induction.  For a selected edge `g₀`,
the bundle count is split according to

```
edgeWeight = main + defect + uniform.
```

The uniform contribution is rewritten by freezing all variables outside
`g₀`.  The defect contribution is bounded by Cauchy--Schwarz; the second
factor is written exactly as an average with two independent copies of the
outside variables.  This is the doubled lower-rank bundle appearing in
Tao's proof.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A finite hypergraph bundle over a fixed finite base hypergraph `H`.
The projection is required to be injective on every bundle edge, and every
bundle edge projects to an edge of `H`. -/
structure HypergraphBundle
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  projection_injective_on_edge :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  projection_mem_base :
    ∀ g ∈ edges, g.image projection ∈ H

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- A bundle is closed under inclusion when every subedge of every bundle
edge is again a bundle edge. -/
def IsClosedUnderInclusion
    (B : HypergraphBundle J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges

/-- The order of a bundle is the largest cardinality of one of its edges.
The empty bundle has order zero. -/
def order (B : HypergraphBundle J K H) : ℕ :=
  B.edges.sup Finset.card





/-- Erase one occurrence edge while retaining the same projection. -/
def eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg)
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)









/-! ## Local tuples and pulled-back base weights -/

/-- Restriction of a full bundle assignment to one occurrence edge. -/
def edgeTuple
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1

/-- Projection gives a bijection from an occurrence edge to its image in
the base vertex set. -/
noncomputable def projectionEquiv
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w hvw
    apply Subtype.ext
    apply B.projection_injective_on_edge g hg v.2 w.2
    exact congrArg Subtype.val hvw
  · intro j
    obtain ⟨v, hv, hvj⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hvj

/-- Transport an occurrence-edge tuple to its projected base edge. -/
noncomputable def projectedEdgeTuple
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.projectionEquiv hg).symm j)

/-- A family of local weights indexed by all finite base edges. -/
abbrev BaseEdgeWeight
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ

/-- Pointwise unit-interval bounds on the edges of a base hypergraph. -/
def BaseWeightsInUnitInterval
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1

/-- Pull a base edge-weight family back along a bundle projection.  Values
away from the bundle edge family are set to one and are never used in the
bundle product. -/
noncomputable def pullbackBaseEdgeWeight
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.projectedEdgeTuple hg y)
  · exact 1





/-! ## Bundle products and normalized counts -/

/-- Unit-interval bounds on an ambient occurrence-edge weight family, on
the edges used by a bundle. -/
def WeightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1



/-- Product of all local edge weights on one full bundle assignment. -/
noncomputable def bundleProduct
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (edgeTuple g x)

/-- Normalized count of a weighted hypergraph bundle. -/
noncomputable def bundleCount
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (B.bundleProduct A)











/-- The product left after removing one selected occurrence edge. -/
noncomputable def edgeRemainder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.eraseEdge g₀).bundleProduct A x

/-- Contribution obtained by placing a local function at one selected edge
and retaining all other bundle factors. -/
noncomputable def edgeContribution
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun x : K → G =>
    q (edgeTuple g₀ x) * B.edgeRemainder g₀ A x)







/-! ## Freezing the outside variables -/

/-- Coordinates outside a selected occurrence edge. -/
abbrev EdgeComplement (g : Finset K) :=
  {v : K // v ∉ g}

/-- Split the occurrence-vertex set into a selected edge and its
complement. -/
noncomputable def edgeSumEquiv (g : Finset K) :
    {v : K // v ∈ g} ⊕ EdgeComplement g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g

/-- Split a full bundle assignment into its selected-edge and outside
coordinates. -/
noncomputable def splitEdgeEquiv
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (EdgeComplement g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (edgeSumEquiv g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        EdgeComplement g => G))







/-- The remaining bundle product after fixing the selected edge tuple and
the outside tuple. -/
noncomputable def edgeRemainderFiber
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G) : ℝ :=
  B.edgeRemainder g₀ A
    ((splitEdgeEquiv g₀).symm (y, z))

/-- Conditional average of the remaining bundle product after the selected
edge tuple is fixed. -/
noncomputable def edgeRemainderAverage
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  mean (B.edgeRemainderFiber g₀ A y)



/-- Inner selected-edge correlation after all outside variables have been
frozen. -/
noncomputable def frozenEdgeCorrelation
    [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (q : ({v : K // v ∈ g₀} → G) → ℝ)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (z : EdgeComplement g₀ → G) : ℝ :=
  mean (fun y =>
    q y * B.edgeRemainderFiber g₀ A y z)





/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

/-- The exact doubled moment created by Cauchy--Schwarz at a selected
edge. -/
noncomputable def doubledRemainderMoment
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : ℝ :=
  mean (fun y =>
    B.edgeRemainderAverage g₀ A y ^ 2)















end HypergraphBundle

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.congr_simp,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.ctorIdx,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.edgeSumEquiv.eq_1,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.edgeTuple.eq_1,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.mk.inj,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.mk.injEq,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.noConfusionType,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.projectedEdgeTuple.congr_simp,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.pullbackBaseEdgeWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.HypergraphBundle.splitEdgeEquiv.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


