-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.mean_indicator_sourceFullTopBadBaseDeletion_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:44:39.303104+00:00
-- url     : https://prove2.me/submissions/e9e51c5c-b9b8-404d-9d56-e6b9e501f779

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_OrderedCoarseFineComplex_mean_indicator_sourceFullOwnAtomBadBaseSupport_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_finsetIndicator_biUnion_le_sum
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_indicator_orderedFacePullbackFinset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Elementary finite Bonferroni bounds

This file records the first two truncations of inclusion--exclusion for a
finite family of zero--one real-valued functions.  The upper bound deliberately
sums ordered pairs of distinct indices; this is a harmless factor-two
overcount that avoids choosing an order on the index type.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized finite mean commutes with a finite sum. -/
theorem mean_finset_sum {α κ : Type*}
    [Fintype α]
    (s : Finset κ) (f : κ → α → ℝ) :
    mean (fun x => ∑ q ∈ s, f q x) =
      ∑ q ∈ s, mean (f q) := by
  simpa [mean] using
    (Finset.expect_sum_comm
      (s := (Finset.univ : Finset α)) s
      (fun x q => f q x))





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
# Bad-base cleaning for ordered hypergraph complexes

For each upper tuple, the frozen fine upper partition chooses a unique
genuine atom.  The tuple is bad when its coarse boundary lies in the bad
base attached to that very atom.  Summing over the disjoint upper atoms gives
the sharp
cleaning estimate

```
mass(own-atom bad base) ≤
  complexity(upper) * densityThreshold
    + atomEnergyGap / defectThreshold.
```

The second half of the file pulls these bad sets back to every subface of a
top ordered edge.  Exact finite Fubini preserves normalized density, and a
finite union bound gives the deletion-cost estimate needed by ordered
hypergraph removal.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Finite union bounds -/



/-- Normalized finite union bound. -/
theorem mean_finsetIndicator_biUnion_le_sum
    {ι Ω : Type*} [DecidableEq Ω]
    [Fintype Ω]
    (s : Finset ι) (F : ι → Finset Ω) :
    mean (finsetIndicator (s.biUnion F)) ≤
      ∑ i ∈ s, mean (finsetIndicator (F i)) := by
  calc
    mean (finsetIndicator (s.biUnion F)) ≤
        mean (fun x => ∑ i ∈ s,
          finsetIndicator (F i) x) :=
      mean_mono (finsetIndicator_biUnion_le_sum s F)
    _ = ∑ i ∈ s, mean (finsetIndicator (F i)) :=
      mean_finset_sum s (fun i => finsetIndicator (F i))

/-! ## The bad base attached to the tuple's own upper atom -/









/-! ## Ordered specialization -/







/-! ## Pullback to top faces -/























/-! ## Surviving tuples induce good closed configurations -/



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
# Source-full good atoms and sharp bad-cell cleaning

The source hypergraph regularity argument tests the square of the usual
fine-immediate-boundary minus coarse-immediate-boundary defect after
conditioning on the join of every proper lower face.  This file implements
that test without changing the defect whose global square mass is paid for
by the ordinary adjacent-boundary atom-energy increment.

For a fixed upper atom, the bad base is the union of

* the usual low coarse-density support, observed on the immediate coarse
  boundary; and
* the support on which the full-lower conditional average of the same
  immediate-boundary defect square exceeds the chosen threshold.

Markov's inequality charges the second support directly to the immediate
atom-energy increment.  Summing over the disjoint upper atoms therefore
gives

```
upperComplexity * α + immediateAtomEnergyGap / β,
```

with no factor involving the complexity of the full-lower partition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedCoarseFineComplex

/-! ## Full-lower large-defect supports -/















/-! ## Low-density union and own-atom accounting -/















/-! ## The coarse upper partition selected by configurations -/





/-- Specialized sharp cleaning estimate for the coarse upper atoms used by
the source mixed counting argument. -/
theorem mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullCoarseOwnAtomBadBaseSupport e α β)) ≤
      (FacePartition.complexity
          (P.coarse.partition e.lowerRank.succ e.face) : ℝ) * α +
        P.coarseUpperFaceAtomEnergyGap
          e.lowerRank e.face / β := by
  unfold sourceFullCoarseOwnAtomBadBaseSupport
    coarseUpperFaceAtomEnergyGap
  exact
    P.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
      e (P.coarse.partition e.lowerRank.succ e.face) hα hβ

end OrderedCoarseFineComplex

/-! ## Avoidance implies source-full mixed goodness -/





namespace ClosedOrderedAtomConfiguration







end ClosedOrderedAtomConfiguration

end Wikipedia.SzemeredisTheorem

end
/-!
# Source-full bad-base cleaning and the ordered removal contradiction

The source-full counting argument conditions the usual adjacent-boundary
square defect on the join of every proper lower face.  `SourceFullGoodAtoms`
shows that cleaning the resulting bad bases nevertheless costs only

```
upper complexity * density threshold + adjacent atom-energy gap / defect threshold.
```

This file pulls those bad bases back to top faces, records the corresponding
normalized deletion bounds, and proves the semantic cover contradiction.  A
tuple surviving every top-face deletion induces its canonical coarse closed
configuration; factorization of each positive face through a top face shows
that this configuration avoids every source-full bad base and is therefore
source-full mixed-good.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex
/-! ## Pulling source-full bad bases back to top faces -/

open Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex in
/-- Direct normalized union-bound cost of one source-full top deletion. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : OrderedFace k r)
    (α β : ℕ → ℝ)
    (hα : ∀ j, 0 ≤ α (j + 1))
    (hβ : ∀ j, 0 < β (j + 1)) :
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
      ∑ q : OrderedPositiveSubface r,
        ((FacePartition.complexity
            (P.coarse.partition q.1.succ
              (q.2.trans e)) : ℝ) *
            α (q.1.1 + 1) +
          P.coarseUpperFaceAtomEnergyGap
              q.1 (q.2.trans e) /
            β (q.1.1 + 1)) := by
  calc
    mean (finsetIndicator
        (P.sourceFullTopBadBaseDeletion e α β)) ≤
        ∑ q : OrderedPositiveSubface r,
          mean (finsetIndicator
            (orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))) := by
      exact
        mean_finsetIndicator_biUnion_le_sum
          (Finset.univ : Finset (OrderedPositiveSubface r))
          (fun q =>
            orderedFacePullbackFinset q.2
              (P.sourceFullCoarseOwnAtomBadBaseSupport
                ({ lowerRank := q.1
                   face := q.2.trans e } :
                  PositiveOrderedFace k r)
                (α (q.1.1 + 1))
                (β (q.1.1 + 1))))
    _ ≤
        ∑ q : OrderedPositiveSubface r,
          ((FacePartition.complexity
              (P.coarse.partition q.1.succ
                (q.2.trans e)) : ℝ) *
              α (q.1.1 + 1) +
            P.coarseUpperFaceAtomEnergyGap
                q.1 (q.2.trans e) /
              β (q.1.1 + 1)) := by
      apply Finset.sum_le_sum
      intro q _hq
      rw [mean_indicator_orderedFacePullbackFinset]
      exact
        P.mean_indicator_sourceFullCoarseOwnAtomBadBaseSupport_le
          ({ lowerRank := q.1
             face := q.2.trans e } : PositiveOrderedFace k r)
          (hα q.1.1) (hβ q.1.1)
