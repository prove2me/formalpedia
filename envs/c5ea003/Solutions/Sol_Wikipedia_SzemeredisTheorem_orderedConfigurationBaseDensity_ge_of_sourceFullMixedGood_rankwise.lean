-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.orderedConfigurationBaseDensity_ge_of_sourceFullMixedGood_rankwise
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:25:05.641149+00:00
-- url     : https://prove2.me/submissions/a8b08fc3-2329-4572-a100-f455690f63ff

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

open Wikipedia.SzemeredisTheorem in
/-- Rankwise source-full goodness supplies the base-density lower bound on
every edge of the ordered-configuration base hypergraph.  Rank zero is the
neutral empty edge and is handled by `α 0 ≤ 1`. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hαzero : α 0 ≤ 1)
    (hgood : A.IsSourceFullMixedGood P α β) :
    ∀ e ∈ orderedConfigurationBaseEdges k r,
      α e.card ≤ orderedConfigurationBaseDensity P A e := by
  intro e he
  by_cases he0 : e = ∅
  · subst e
    simpa using hαzero
  · have hene : e.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr he0
    have her : e.card ≤ r :=
      (mem_orderedConfigurationBaseEdges_iff e).1 he
    have hdensity :=
      (hgood (positiveOrderedFaceOfEdge e hene her)).1
    have hrank :
        (positiveOrderedFaceOfEdge e hene her).rank = e.card := by
      rw [← positiveOrderedFaceEdge_card,
        positiveOrderedFaceEdge_ofEdge]
    rw [hrank] at hdensity
    simpa [sourceFullMixedCoarseDensity,
      orderedConfigurationBaseDensity, hene, her] using hdensity
