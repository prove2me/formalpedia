-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.281779+00:00
-- url     : https://prove2.me/submissions/a62da746-4702-4483-a844-20241ee7407f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_extendConfigurationFaceTuple_projection
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_sourceFullMixedBoundaryWeight_eq_strictFaceProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_strictBoundaryLocalProduct_edgeTuple
import Theorems.Thm_Wikipedia_SzemeredisTheorem_positiveOrderedFaceEdge_injective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

section



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



namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}



















/-! ## Local tuples and pulled-back base weights -/













@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]



/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/







@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

/-- Recombining a selected-edge tuple and an outside tuple recovers the
selected-edge tuple on restriction. -/
@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp















/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/















/-! ## The lower-order and strict-boundary filtrations -/

















@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl











/-! ## Main-density products -/













/-! ## The main product under duplication -/













end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}









/-- The forward map of `projectionEquiv` is the bundle projection. -/
@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Bernoulli reduction for bounded boundary products

The preliminary shared-face regularity lemma is stated using Boolean
products on the immediate boundary of an upper face.  This file proves that
this loses no generality for products of arbitrary `[0,1]`-valued boundary
factors.

At successor arity the ordinary `CutTestFamily` coordinates are exactly the
boundary coordinates.  The only formal difference is that
`BooleanCutAssignment` uses an uncurried product index whereas
`BoundaryBooleanCutAssignment` is curried.  After recording the equivalence
between those two presentations, the finite Bernoulli-mixture identities
from `BooleanCutReduction` give:

* every bounded boundary factor is a convex average of Boolean component
  indicators;
* every bounded boundary product is a convex average of
  `boundaryBooleanCutSupport` indicators;
* Boolean preliminary regularity therefore controls every bounded boundary
  product with the same error.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators





















/-- At successor arity the specialized boundary erasure is the ordinary
cut-test coordinate erasure. -/
theorem eraseBoundaryCoordinate_eq_eraseCoordinate
    {G : Type*} {j : ℕ}
    (i : Fin (j + 1)) (x : Fin (j + 1) → G) :
    eraseBoundaryCoordinate i x = eraseCoordinate i x :=
  rfl









namespace FaceRegularityState





end FaceRegularityState





end Wikipedia.SzemeredisTheorem

end

section






/-!
# Positive counts for good closed ordered configurations

This file turns the local good-atom estimates into a direct positive-count
recurrence.  The edge index contains every positive-rank ordered face of an
ordered partition complex.  On downward-closed face families, the count is
the normalized mean of the selected atom indicators.  On other families we
use the exact product of the coarse densities; this total extension lets us
apply the finite abstract recurrence without asking localized estimates on
families which omit their boundary.

At a maximum-rank face, the remaining product contains every proper
boundary factor.  Thus it is supported on the canonical coarse boundary
atom.  The identity

```text
1_A = p + (E_fine 1_A - p) + (1_A - E_fine 1_A)
```

then gives the recurrence.  The uniform term is tested against a bounded
boundary product after freezing the outside variables.  The defect term is
bounded by localized Cauchy--Schwarz; the boundary support and unit bounds
make its square at most the good-atom defect threshold.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive-rank faces and immediate downward closure -/



namespace PositiveOrderedFace







@[simp]
theorem rank_pos {k r : ℕ} (e : PositiveOrderedFace k r) :
    0 < e.rank := by
  simp [rank]









end PositiveOrderedFace











/-! ## Missing coordinates for lower-or-equal rank faces -/











/-! ## Selected atom weights and counts -/





















/-! ## Freezing and grouping a maximum-rank remainder -/













/-! ## Coarse densities, defects, and boundary support -/



























/-! ## Selected-face contributions and exact decomposition -/











/-! ## Uniform contribution -/





/-! ## Localized defect contribution -/















/-! ## The one-face recurrence -/













/-! ## Quantitative full-count lower bound and positivity -/





end Wikipedia.SzemeredisTheorem

end

section





/-!
# The ordered configuration as an initial hypergraph bundle

The generalized bundle counting lemma starts from the bundle having one
occurrence vertex above each vertex class.  Its edges are the empty edge
and the ranges of all positive ordered faces.  This file identifies that
initial bundle, its indicator weights, and its main-density product with
the ordered-configuration objects used by the removal argument.

The only small bookkeeping issue is that an ordered face is an increasing
map `Fin n ↪o Fin k`, whereas a bundle edge is a `Finset (Fin k)`.  A
nonempty finite set has a unique increasing enumeration, supplied by
`Finset.orderEmbOfFin`; the equivalence below packages this canonical
change of indices.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive ordered faces as nonempty finite edges -/





theorem positiveOrderedFaceEdge_nonempty
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).Nonempty := by
  apply Finset.card_pos.mp
  rw [positiveOrderedFaceEdge_card]
  exact e.rank_pos

















/-! ## The complete initial bundle -/

















/-! ## Canonical local tuples and base weights -/







@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]







/-! ## Main densities -/









/-! ## Exact initial count and product identities -/













end Wikipedia.SzemeredisTheorem

end

section


/-!
# Full lower boundaries of ordered faces

The source hypergraph regularity argument conditions an upper face on the
join of the partitions carried by *all* of its nonempty proper subfaces.
The adjacent-rank boundary in `OrderedBoundaryPartition` is enough to encode
closedness, but it does not expose this source-level sigma algebra directly.

This file constructs that full lower boundary.  A proper positive subface of
an `n + 1` tuple is represented by a positive ordered face of that tuple
whose rank is at most `n`.  Each genuine partition in the ambient ordered
complex is pulled back to the selected upper tuple space, and the full lower
boundary is their finite common refinement.

The last section packages the coarse/fine defect and the corresponding
source mixed-goodness condition.  Its principal consequence is the localized
weighted square-defect estimate on the selected full-lower atom.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Proper positive subfaces -/





/-! ## The full lower partition -/







/-- Restricting through the ambient face agrees with first selecting the
upper tuple and then selecting its local proper subface. -/
@[simp]
theorem orderedFaceTuple_orderedFullLowerAmbientFace
    {G : Type*} {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1)
    (x : Fin k → G) :
    orderedFaceTuple (orderedFullLowerAmbientFace e d) x =
      orderedFaceTuple d.face (orderedFaceTuple e.face x) :=
  rfl























/-! ## Selected full-lower atoms and their weights -/





















/-! ## Source full-lower goodness -/























end Wikipedia.SzemeredisTheorem

end

section



/-!
# Source-full goodness supplies the bundle-localized defect bound

For a maximal nonempty occurrence edge of a closed bundle, projection is a
bijection onto the corresponding base edge.  Consequently its strict
occurrence boundary is just another indexing of all proper subsets of that
base edge.  The product of the configuration indicators on those subsets is
the indicator of the full lower atom used in `OrderedFullBoundary`.

This file makes that reindexing explicit.  It then transports the source-full
localized square estimate along the induced equivalence of tuple spaces.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## Tuple reindexing -/



@[simp]
theorem projectedEdgeOrderIso_apply_val
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (i : Fin ((B.orderedConfigurationBundleFace
      hg hne).lowerRank.1 + 1)) :
    ((B.projectedEdgeOrderIso hg hne) i).1 =
      (B.orderedConfigurationBundleFace hg hne).face i := by
  rfl





/-! ## Proper subfaces -/











@[simp]
theorem mem_orderedConfigurationStrictFaceFamily
    (e f : PositiveOrderedFace k r) :
    f ∈ orderedConfigurationStrictFaceFamily e ↔
      positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e := by
  simp [orderedConfigurationStrictFaceFamily]



/-! ## The full-lower atom as a strict-face product -/









/-! ## Reindexing a closed bundle boundary -/



theorem liftProjectedSubedge_subset
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    B.liftProjectedSubedge g₀ t ⊆ g₀ := by
  exact Finset.filter_subset _ _

theorem image_liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) {t : Finset (Fin k)}
    (ht : t ⊆ g₀.image B.projection) :
    (B.liftProjectedSubedge g₀ t).image B.projection = t := by
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hv).2
  · intro hj
    obtain ⟨v, hvg, hvj⟩ :=
      Finset.mem_image.mp (ht hj)
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨hvg, ?_⟩, hvj⟩
    exact hvj ▸ hj

theorem liftProjectedSubedge_image_eq
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hgg₀ : g ⊆ g₀) :
    B.liftProjectedSubedge g₀
        (g.image B.projection) = g := by
  ext v
  constructor
  · intro hv
    have hvg₀ := (Finset.mem_filter.mp hv).1
    obtain ⟨w, hwg, hwv⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hv).2
    have hwg₀ : w ∈ g₀ := hgg₀ hwg
    have hwv' : w = v :=
      B.projection_injective_on_edge g₀ hg₀ hwg₀ hvg₀ hwv
    exact hwv' ▸ hwg
  · intro hv
    exact Finset.mem_filter.mpr
      ⟨hgg₀ hv,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-! The substantial pointwise identity. -/



/-! ## Transport of the localized estimate -/





end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end
/-!
# Source-full goodness supplies the bundle-localized defect bound

For a maximal nonempty occurrence edge of a closed bundle, projection is a
bijection onto the corresponding base edge.  Consequently its strict
occurrence boundary is just another indexing of all proper subsets of that
base edge.  The product of the configuration indicators on those subsets is
the indicator of the full lower atom used in `OrderedFullBoundary`.

This file makes that reindexing explicit.  It then transports the source-full
localized square estimate along the induced equivalence of tuple spaces.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
/-! ## Tuple reindexing -/
/-! ## Proper subfaces -/
/-! ## The full-lower atom as a strict-face product -/
/-! ## Reindexing a closed bundle boundary -/
/-! The substantial pointwise identity. -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
theorem solution
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (y : {v : K // v ∈ g₀} → G) :
    B.strictBoundaryLocalProduct g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) y =
      sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)
        (B.orderedConfigurationBundleFaceTuple hg₀ hne y) := by
  classical
  let e := B.orderedConfigurationBundleFace hg₀ hne
  let u := B.orderedConfigurationBundleFaceTuple hg₀ hne y
  let x := extendConfigurationFaceTuple P A e u
  have heedge :
      positiveOrderedFaceEdge e =
        g₀.image B.projection := by
    dsimp [e, orderedConfigurationBundleFace]
    exact positiveOrderedFaceEdge_ofEdge
      (g₀.image B.projection)
      (B.projectedEdge_nonempty hg₀ hne)
      (B.projectedEdge_card_le hg₀)
  let z : EdgeComplement g₀ → G :=
    fun v => A.witness (B.projection v.1)
  let xK : K → G :=
    (splitEdgeEquiv g₀).symm (y, z)
  have hxK : edgeTuple g₀ xK = y := by
    exact edgeTuple_splitEdgeEquiv_symm g₀ y z
  have hlocalProduct :
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK := by
    calc
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A))
          (edgeTuple g₀ xK) := by
            rw [hxK]
      _ =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK :=
        B.strictBoundaryLocalProduct_edgeTuple g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK
  have hempty : ∅ ∈ (B.strictBoundary g₀).edges := by
    apply (B.mem_strictBoundary_edges g₀ ∅).2
    refine ⟨hclosed hg₀ (Finset.empty_subset g₀), ?_⟩
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.empty_subset _, hne.ne_empty.symm⟩
  have hemptyWeight :
      B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (edgeTuple ∅ xK) = 1 := by
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      ((B.mem_strictBoundary_edges g₀ ∅).1 hempty).1]
    exact orderedConfigurationBaseWeight_empty A _
  rw [hlocalProduct]
  rw [sourceFullMixedBoundaryWeight_eq_strictFaceProduct P A e u]
  unfold bundleProduct partialConfigurationWeight
  rw [← Finset.prod_erase_mul _ _ hempty,
    hemptyWeight, mul_one]
  apply Finset.prod_bij
    (fun g _hg =>
      positiveOrderedFaceOfEdge
        (g.image B.projection)
        (Finset.image_nonempty.mpr
          (Finset.nonempty_iff_ne_empty.mpr
            (Finset.mem_erase.mp _hg).1))
        (B.projectedEdge_card_le
          (((B.mem_strictBoundary_edges g₀ g).1
            (Finset.mem_of_mem_erase _hg)).1)))
  · intro g hg
    simp only [Finset.mem_erase] at hg
    rw [mem_orderedConfigurationStrictFaceFamily]
    rw [positiveOrderedFaceEdge_ofEdge]
    rw [heedge]
    have hgstrict :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2
    constructor
    · intro j hj
      obtain ⟨v, hvg, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr
        ⟨v, hgstrict.1 hvg, rfl⟩
    · intro hreverse
      apply hgstrict.2
      intro v hvg₀
      obtain ⟨w, hwg, hwv⟩ :=
        Finset.mem_image.mp
          (hreverse
            (Finset.mem_image.mpr
              ⟨v, hvg₀, rfl⟩))
      have hwg₀ : w ∈ g₀ := hgstrict.1 hwg
      have hwv' : w = v :=
        B.projection_injective_on_edge
          g₀ hg₀ hwg₀ hvg₀ hwv
      exact hwv' ▸ hwg
  · intro g₁ hg₁ g₂ hg₂ heq
    have himage :
        g₁.image B.projection =
          g₂.image B.projection := by
      simpa only [positiveOrderedFaceEdge_ofEdge] using
        congrArg positiveOrderedFaceEdge heq
    have hg₁sub :=
      ((B.mem_strictBoundary_edges g₀ g₁).1
        (Finset.mem_of_mem_erase hg₁)).2.1
    have hg₂sub :=
      ((B.mem_strictBoundary_edges g₀ g₂).1
        (Finset.mem_of_mem_erase hg₂)).2.1
    rw [← B.liftProjectedSubedge_image_eq hg₀ hg₁sub,
      ← B.liftProjectedSubedge_image_eq hg₀ hg₂sub,
      himage]
  · intro f hf
    have hfe :=
      (mem_orderedConfigurationStrictFaceFamily e f).1 hf
    let t := positiveOrderedFaceEdge f
    let g := B.liftProjectedSubedge g₀ t
    have ht : t ⊆ g₀.image B.projection := by
      simpa [e, orderedConfigurationBundleFace,
        positiveOrderedFaceEdge_ofEdge] using hfe.1
    have hgsub : g ⊆ g₀ :=
      B.liftProjectedSubedge_subset g₀ t
    have hgmem : g ∈ B.edges :=
      hclosed hg₀ hgsub
    have himage : g.image B.projection = t :=
      B.image_liftProjectedSubedge g₀ ht
    have hgne : g ≠ ∅ := by
      intro hzero
      have : t = ∅ := by simpa [hzero] using himage.symm
      have htne := positiveOrderedFaceEdge_nonempty f
      change t.Nonempty at htne
      rw [this] at htne
      exact Finset.not_nonempty_empty htne
    have hgproper : g ⊂ g₀ := by
      refine ⟨hgsub, ?_⟩
      intro hgg
      have hgeq : g = g₀ :=
        Finset.Subset.antisymm hgsub hgg
      have : t = g₀.image B.projection := by
        rw [← himage, hgeq]
      apply hfe.2
      rw [heedge, ← this]
    refine ⟨g, Finset.mem_erase.mpr
      ⟨hgne,
        (B.mem_strictBoundary_edges g₀ g).2
          ⟨hgmem, hgproper⟩⟩, ?_⟩
    apply positiveOrderedFaceEdge_injective
    simpa only [positiveOrderedFaceEdge_ofEdge] using himage
  · intro g hg
    simp only [Finset.mem_erase] at hg
    have hgB :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).1
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A) hgB]
    unfold orderedConfigurationBaseWeight
    simp only [dif_pos (Finset.image_nonempty.mpr
      (Finset.nonempty_iff_ne_empty.mpr hg.1))]
    simp only [dif_pos (B.projectedEdge_card_le hgB)]
    congr 1
    have hgne : g.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hg.1
    change
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) =
        orderedFaceTuple
          (B.orderedConfigurationBundleFace hgB hgne).face x
    funext i
    let v : {v : K // v ∈ g} :=
      (B.projectionEquiv hgB).symm
        (B.projectedEdgeOrderIso hgB hgne i)
    have hgsub :
        g ⊆ g₀ :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2.1
    let v₀ : {v : K // v ∈ g₀} :=
      ⟨v.1, hgsub v.2⟩
    have hprojection :
        (B.orderedConfigurationBundleFace hgB hgne).face i =
          B.projection v₀.1 := by
      calc
        (B.orderedConfigurationBundleFace hgB hgne).face i =
            (B.projectedEdgeOrderIso hgB hgne i).1 := by
          rw [B.projectedEdgeOrderIso_apply_val]
        _ = ((B.projectionEquiv hgB) v).1 := by
          rw [Equiv.apply_symm_apply]
        _ = B.projection v.1 :=
          B.projectionEquiv_apply_val hgB v
        _ = B.projection v₀.1 := rfl
    calc
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) i =
          xK v.1 := by
        rfl
      _ = y v₀ := by
        have hv := congrFun hxK v₀
        exact hv
      _ = x (B.projection v₀.1) := by
        symm
        exact
          B.extendConfigurationFaceTuple_projection
            P A hg₀ hne y v₀
      _ =
          orderedFaceTuple
            (B.orderedConfigurationBundleFace hgB hgne).face
            x i := by
        rw [orderedFaceTuple, hprojection]
