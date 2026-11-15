-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.orderedConfigurationInitialBundle_bundleMainProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.466866+00:00
-- url     : https://prove2.me/submissions/47c5af9f-363b-4657-9ba9-b168196593fa

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
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











@[simp]
theorem positiveOrderedFaceOfEdge_edge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    positiveOrderedFaceOfEdge
        (positiveOrderedFaceEdge e)
        (positiveOrderedFaceEdge_nonempty e)
        (positiveOrderedFaceEdge_card_le e) = e := by
  apply positiveOrderedFaceEdge_injective
  exact positiveOrderedFaceEdge_ofEdge
    (positiveOrderedFaceEdge e)
    (positiveOrderedFaceEdge_nonempty e)
    (positiveOrderedFaceEdge_card_le e)





/-! ## The complete initial bundle -/





theorem empty_not_mem_positiveOrderedFaceEdge_image
    (k r : ℕ) :
    (∅ : Finset (Fin k)) ∉
      Finset.univ.image
        (positiveOrderedFaceEdge :
          PositiveOrderedFace k r → Finset (Fin k)) := by
  intro h
  obtain ⟨e, _he, hedge⟩ :=
    Finset.mem_image.mp h
  exact (positiveOrderedFaceEdge_nonempty e).ne_empty
    hedge





@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl

@[simp]
theorem orderedConfigurationInitialBundle_projection
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).projection =
      id :=
  rfl



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

@[simp]
theorem orderedConfigurationBaseDensity_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    orderedConfigurationBaseDensity P A
        (positiveOrderedFaceEdge e) =
      mixedConfigurationCoarseDensity P A e := by
  classical
  unfold orderedConfigurationBaseDensity
  simp only [dif_pos (positiveOrderedFaceEdge_nonempty e)]
  have hcard :
      (positiveOrderedFaceEdge e).card ≤ r := by
    simpa [positiveOrderedFaceEdge_card] using
      positiveOrderedFaceEdge_card_le e
  simp only [dif_pos hcard]
  exact congrArg (mixedConfigurationCoarseDensity P A)
    (positiveOrderedFaceOfEdge_edge e)



/-! ## Exact initial count and product identities -/













end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Positive ordered faces as nonempty finite edges -/
/-! ## The complete initial bundle -/
/-! ## Canonical local tuples and base weights -/
/-! ## Main densities -/
/-! ## Exact initial count and product identities -/

open Wikipedia.SzemeredisTheorem in
/-- The main product of the initial bundle is the product of all mixed
coarse densities; the extra empty-edge factor is one. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    (orderedConfigurationInitialBundle k r).bundleMainProduct
          (orderedConfigurationBaseDensity P A) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      orderedConfigurationBaseDensity P A
        (g.image
          (orderedConfigurationInitialBundle k r).projection)) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [orderedConfigurationInitialBundle_edges,
    orderedConfigurationInitialBundle_projection]
  simp only [Function.id_def, Finset.image_id']
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      orderedConfigurationBaseDensity P A g) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r),
    orderedConfigurationBaseDensity_empty,
    one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  simp
