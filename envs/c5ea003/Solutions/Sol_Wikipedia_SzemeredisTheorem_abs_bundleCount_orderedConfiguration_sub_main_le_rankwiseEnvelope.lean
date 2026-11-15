-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.abs_bundleCount_orderedConfiguration_sub_main_le_rankwiseEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:42.415085+00:00
-- url     : https://prove2.me/submissions/d67a1290-283c-4343-ad05-f991d3a9679a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenUniformity
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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_FaceRegularityState_abs_faceCutCorrelation_le_of_boundaryBoolean
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_hasOrderedConfigurationBundleFrozenCutRepresentation
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_hasTaoBundleCountingStep_orderedConfiguration
import Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedConfigurationBaseWeight_idempotent
import Theorems.Thm_Wikipedia_SzemeredisTheorem_orderedConfigurationBaseWeight_unitInterval

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











@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl







/-! ## Local tuples and pulled-back base weights -/

















/-! ## Bundle products and normalized counts -/





























/-! ## Freezing the outside variables -/

























/-! ## Localized Cauchy--Schwarz and the doubled remainder -/

















end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}





























































@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl































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
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl













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



/-- Boolean preliminary ordered regularity implies bounded-test preliminary
ordered regularity with exactly the same error. -/
theorem IsPreliminaryOrderedRegular.toBounded
    {G : Type*} [Fintype G] [DecidableEq G]
    {k j : ℕ}
    {lower : OrderedFacePartitionSystem G k j}
    {upper : OrderedFacePartitionSystem G k (j + 1)}
    {ε : ℝ}
    (hregular :
      IsPreliminaryOrderedRegular lower upper ε) :
    IsPreliminaryOrderedBoundedRegular
      lower upper ε := by
  intro e a u hu
  exact
    FaceRegularityState.abs_faceCutCorrelation_le_of_boundaryBoolean
      (⟨orderedBoundaryPartition lower e⟩ :
        FaceRegularityState (Fin (j + 1) → G))
      (partitionAtomIndicator (upper e) a)
      u hu (fun b => hregular e a b)

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Positive counts for mixed-good coarse configurations

A closed configuration in this file selects atoms of the coarse complex.
The selected coarse upper atom is decomposed using conditional expectation
first on the fine lower boundary and then on the coarse lower boundary.
Thus the main density and defect are exactly those controlled by
`ClosedOrderedAtomConfiguration.IsMixedGood`, while the uniform term is
controlled by regularity of the fine lower boundary against the coarse upper
partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A diagonal pair used only for coarse boundary support -/



/-! ## Mixed coarse/fine conditional decomposition -/





















/-! ## Coarse boundary support and selected-face decomposition -/







/-! ## Mixed coarse-upper regularity and the uniform contribution -/





/-- Mixed all-rank preliminary regularity specializes to the selected coarse
upper atom at a positive face. -/
theorem mixedConfigurationFace_isFaceCutRegular
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : OrderedRegularityTolerance r)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P τ)
    (e : PositiveOrderedFace k r) :
    (⟨orderedBoundaryPartition
        (positiveFaceLowerLayer P.fine e) e.face⟩ :
      FaceRegularityState
        (Fin (e.lowerRank.1 + 1) → G)).IsFaceCutRegular
      (partitionAtomIndicator
        (P.coarse.partition e.lowerRank.succ e.face)
        (A.atom e.lowerRank.succ e.face))
      (τ e.lowerRank) := by
  rw [positiveFaceLowerLayer]
  exact
    (hregular e.lowerRank).toBounded
      e.face
      (A.atom e.lowerRank.succ e.face)









/-! ## Localized mixed defect contribution -/











/-! ## One-face recurrence -/





/-! ## Rank-dependent totalized recurrence -/











/-! ## Rankwise full-count lower bounds -/





/-! ## Fine-regular complexity corollaries -/





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



@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]





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
# Frozen bundle uniformity

This file records the exact interface between mixed preliminary
regularity and the frozen-uniformity input of generalized bundle
counting.

For a selected occurrence edge `g₀`, preliminary regularity applies on
the canonically enumerated projected face.  What remains is a purely
combinatorial representation statement: after the occurrence variables
outside `g₀` have been fixed, the erased bundle product is a bounded
lower-face cut test on that projected face.

The representation is separated from the analytic implication for two
reasons.

* It makes explicit that no stronger analytic regularity lemma is needed.
  Ordinary bounded face-cut regularity is exactly the required norm.
* It gives the source-style regularity certificate a precise target while
  the dependent reindexing of arbitrary bundle vertices is developed.

The key combinatorial fact behind the representation is that every
remaining occurrence edge omits a vertex of `g₀`: if it contained all of
`g₀`, maximality of `g₀` would force equality, contradicting its presence
in the erased edge family.  Injectivity of the bundle projection on
`g₀` transports such a missing occurrence vertex to a missing coordinate
of the canonical positive ordered face.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## A missing selected vertex -/



/-! ## The selected face regularity state -/





/-! ## The exact combinatorial transport obligation -/



/-! ## Preliminary regularity gives the frozen estimate -/

/-- Common-tolerance mixed preliminary regularity gives frozen bundle
uniformity once the remainder has been reindexed as a bounded face cut. -/
theorem hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (τ : ℝ)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (hcut :
      HasOrderedConfigurationBundleFrozenCutRepresentation P A) :
    HasOrderedConfigurationBundleFrozenUniformity P A τ := by
  intro K _instK _decK B hclosed g₀ hg₀ hmax hne z
  obtain ⟨u, hu, hreindex⟩ :=
    hcut K B hclosed hg₀ hmax hne z
  rw [hreindex]
  exact
    mixedConfigurationFace_isFaceCutRegular
      P A (fun _ => τ) hregular
      (B.orderedConfigurationBundleFace hg₀ hne)
      u hu

/-! ## Source-full certificate -/





end HypergraphBundle

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Rankwise source-full bundle counting

The source full-regularity hierarchy supplies a different density and
defect threshold at each positive rank, together with one common
fine-boundary regularity error.  This file assembles those data directly
with the generalized bundle-counting envelope.

Unlike `SourceFullBundleCounting`, no parameter is required to be constant
in the rank.  The final lower bound is quantitative: if the chosen envelope
has error below one half, then every source-full good closed configuration
has count at least one half of the product of its prescribed rankwise
density floors.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## The finite horizon of the initial configuration bundle -/



/-! ## The source-full regularity certificate as a counting input -/



/-! ## Rankwise base-density and one-edge inputs -/



/-- Rankwise source-full localized defects and a common frozen-uniformity
bound give the one-edge input used by relative generalized counting. -/
theorem hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ) (τ : ℝ)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ)) :
    HasTaoBundleCountingStep
      (H := orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      β τ := by
  apply HypergraphBundle.hasTaoBundleCountingStep_orderedConfiguration
      P A β τ hβ hτ
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
        P A α β hgood
  · exact
      HypergraphBundle.hasOrderedConfigurationBundleFrozenUniformity_of_fullyMixed
        P A τ hregular
        (HypergraphBundle.hasOrderedConfigurationBundleFrozenCutRepresentation
          P A)

/-! ## Relative counting with an arbitrary rankwise envelope -/



/-! ## Initial configuration and a uniform quantitative lower bound -/







end Wikipedia.SzemeredisTheorem

end
/-!
# Rankwise source-full bundle counting

The source full-regularity hierarchy supplies a different density and
defect threshold at each positive rank, together with one common
fine-boundary regularity error.  This file assembles those data directly
with the generalized bundle-counting envelope.

Unlike `SourceFullBundleCounting`, no parameter is required to be constant
in the rank.  The final lower bound is quantitative: if the chosen envelope
has error below one half, then every source-full good closed configuration
has count at least one half of the product of its prescribed rankwise
density floors.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## The finite horizon of the initial configuration bundle -/
/-! ## The source-full regularity certificate as a counting input -/
/-! ## Rankwise base-density and one-edge inputs -/
/-! ## Relative counting with an arbitrary rankwise envelope -/

open Wikipedia.SzemeredisTheorem in
/-- General source-full relative counting with rankwise density and defect
arrays and an arbitrary valid bundle-counting envelope. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hβ : ∀ d, 0 ≤ β d)
    (hτ : 0 ≤ τ)
    (hgood : A.IsSourceFullMixedGood P α β)
    (hregular :
      IsFullyMixedPreliminaryOrderedRegular P (fun _ => τ))
    (henvelope : IsBundleCountingEnvelope α β μ τ E)
    {K : Type} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion) :
    |B.bundleCount
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) -
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A)| ≤
      E B.order B.edges.card *
        B.bundleMainProduct
          (orderedConfigurationBaseDensity P A) := by
  exact
    @abs_bundleCount_pullback_sub_bundleMainProduct_le_envelope
      (Fin k) G inferInstance inferInstance
      (orderedConfigurationBaseEdges k r) inferInstance
      (orderedConfigurationBaseWeight A)
      (orderedConfigurationBaseDensity P A)
      α β μ τ E
      (orderedConfigurationBaseWeight_unitInterval A)
      (orderedConfigurationBaseWeight_idempotent A)
      (orderedConfigurationBaseWeight_empty A)
      (orderedConfigurationBaseDensity_empty P A)
      (orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
        P A α β hαzero hgood)
      (hasTaoBundleCountingStep_orderedConfiguration_of_sourceFull_rankwise
        P A α β τ hβ hτ hgood hregular)
      henvelope K inferInstance inferInstance B hclosed
