-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:45:55.932987+00:00
-- url     : https://prove2.me/submissions/4536cc7e-104f-4933-b7cc-87e429da5a26

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_mean_splitEdge
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_pullbackBaseEdgeWeight_eq_of_projection_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_strictBoundaryLocalProduct_edgeTuple
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Normalized averages on finite types

The Green--Tao argument repeatedly averages real-valued functions over finite
cyclic groups and finite products of such groups.  This file fixes one
normalization and records the elementary algebraic and order lemmas used by
the transference layer.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators











@[simp]
theorem mean_empty {α : Type*} [Fintype α] [IsEmpty α] (f : α → ℝ) :
    mean f = 0 := by
  simp [mean]























end Wikipedia.SzemeredisTheorem

end

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
# The arithmetic-progression/simplex correspondence

For `k = r + 2`, the coordinate moment and the negative coordinate sum give
the initial term and common difference of the encoded cyclic progression.
The remaining `r` coordinates parametrize every fiber uniformly.  An
explicit equivalence records this change of variables and transports the
normalized simplex average to the normalized arithmetic-progression count.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators























/-- Normalized averages are invariant under an equivalence of finite
indexing types. -/
theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h







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
# Relative generalized counting for closed hypergraph bundles

This file performs the double induction in Tao's generalized counting
lemma.  Its sole analytic input is `HasTaoBundleCountingStep`: at one
maximal occurrence edge, the count differs from the main density times
the erased count by the square root of two lower-order counts plus the
common frozen-uniformity error.

The induction first decreases bundle order and then, at fixed order,
decreases the number of occurrence edges.  The exact main-product
identities from `HypergraphBundleGeneralizedCounting` cancel every
lower-order density from the relative defect error.  Consequently the
defect term pays only the selected-rank floor `α`, while the absolute
uniform term pays the all-rank floor `μ`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Canonical pullbacks on subbundles -/

/-- On a subbundle with the same occurrence projection, pulling a base
weight back before or after passing to the subbundle gives the same
bundle product. -/
theorem bundleProduct_pullback_eq_of_subset_of_projection_eq
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G)
    (x : K → G) :
    C.bundleProduct (B.pullbackBaseEdgeWeight A) x =
      C.bundleProduct (C.pullbackBaseEdgeWeight A) x := by
  unfold bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  exact B.pullbackBaseEdgeWeight_eq_of_projection_eq
    C A hprojection (hCB hg) hg (edgeTuple g x)

/-- Count-level version of canonical pullback invariance. -/
theorem bundleCount_pullback_eq_of_subset_of_projection_eq
    [Fintype K] [Fintype G]
    (B C : HypergraphBundle J K H)
    (hCB : C.edges ⊆ B.edges)
    (hprojection : B.projection = C.projection)
    (A : BaseEdgeWeight J G) :
    C.bundleCount (B.pullbackBaseEdgeWeight A) =
      C.bundleCount (C.pullbackBaseEdgeWeight A) := by
  unfold bundleCount
  apply congrArg mean
  funext x
  exact B.bundleProduct_pullback_eq_of_subset_of_projection_eq
    C hCB hprojection A x



/-! ## Structural bounds for the two outer-induction bundles -/







/-! ## Elementary main-product and induction helpers -/











end HypergraphBundle

/-! ## The analytic one-edge interface -/

universe uJ uG

variable {J : Type uJ} {G : Type uG}
  [DecidableEq J] [Fintype G] [DecidableEq G]
  {H : Finset (Finset J)}



/-! ## Full double induction -/



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







omit [Fintype G] [DecidableEq G] in
@[simp]
theorem orderedConfigurationBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.orderedConfigurationBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold orderedConfigurationBundleFaceTupleEquiv
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple projectedEdgeOrderIso
  rfl

/-! ## Proper subfaces -/















/-! ## The full-lower atom as a strict-face product -/









/-! ## Reindexing a closed bundle boundary -/









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
/-! ## Transport of the localized estimate -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
theorem solution
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty) :
    (B.strictBoundary g₀).bundleCount
        ((B.strictBoundary g₀).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) =
      mean (sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)) := by
  classical
  rw [← B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.strictBoundary g₀)
    (Finset.filter_subset _ _)
    rfl
    (orderedConfigurationBaseWeight A)]
  cases isEmpty_or_nonempty G with
  | inl hG =>
      let : IsEmpty G := hG
      have : Nonempty K := ⟨hne.choose⟩
      have :
          Nonempty
            (Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1)) :=
        ⟨⟨0, Nat.succ_pos _⟩⟩
      simp only [bundleCount, mean_empty]
  | inr hG =>
      let : Nonempty G := hG
      unfold bundleCount
      rw [mean_splitEdge g₀]
      unfold mean₂
      have hfiber :
          ∀ y : {v : K // v ∈ g₀} → G,
            mean (fun z : EdgeComplement g₀ → G =>
                (B.strictBoundary g₀).bundleProduct
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A))
                  ((splitEdgeEquiv g₀).symm (y, z))) =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv
                  hg₀ hne y) := by
        intro y
        calc
          mean (fun z : EdgeComplement g₀ → G =>
              (B.strictBoundary g₀).bundleProduct
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))
                ((splitEdgeEquiv g₀).symm (y, z))) =
              mean (fun _z : EdgeComplement g₀ → G =>
                B.strictBoundaryLocalProduct g₀
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A)) y) := by
            apply congrArg mean
            funext z
            rw [← B.strictBoundaryLocalProduct_edgeTuple g₀
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z))]
            rw [edgeTuple_splitEdgeEquiv_symm]
          _ =
              B.strictBoundaryLocalProduct g₀
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) y := by
            exact mean_const _
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTuple hg₀ hne y) :=
            B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
              P A hclosed hg₀ hne y
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y) := by
            rw [orderedConfigurationBundleFaceTupleEquiv_apply]
      rw [show
        (fun y : {v : K // v ∈ g₀} → G =>
          mean (fun z : EdgeComplement g₀ → G =>
            (B.strictBoundary g₀).bundleProduct
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z)))) =
          fun y =>
            sourceFullMixedBoundaryWeight P A
              (B.orderedConfigurationBundleFace hg₀ hne)
              (B.orderedConfigurationBundleFaceTupleEquiv
                hg₀ hne y) by
        funext y
        exact hfiber y]
      exact mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
        (fun y =>
          sourceFullMixedBoundaryWeight P A
            (B.orderedConfigurationBundleFace hg₀ hne)
            (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y))
        (sourceFullMixedBoundaryWeight P A
          (B.orderedConfigurationBundleFace hg₀ hne))
        (fun _ => rfl)
