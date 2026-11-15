-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration.isSourceFullMixedGood_of_avoids_sourceFullTopBadBaseDeletion
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:47:17.968086+00:00
-- url     : https://prove2.me/submissions/099c4530-2838-43c1-94e5-a14581f38098

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_ClosedOrderedAtomConfiguration_sourceFullMixedGoodAtFace_of_not_mem_badBase
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_orderedFace_factor_through

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





/-! ## The bad base attached to the tuple's own upper atom -/









/-! ## Ordered specialization -/







/-! ## Pullback to top faces -/







@[simp]
theorem mem_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G))
    (y : Fin r → G) :
    y ∈ orderedFacePullbackFinset d S ↔
      orderedFaceTuple d y ∈ S := by
  simp [orderedFacePullbackFinset]















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







end OrderedCoarseFineComplex

/-! ## Avoidance implies source-full mixed goodness -/





namespace ClosedOrderedAtomConfiguration





/-- Simultaneous avoidance of the source-full bad base at every positive
face implies the all-face source-goodness predicate used by counting. -/
theorem isSourceFullMixedGood_of_avoids_badBases
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (havoid : A.AvoidsSourceFullBadBases P α β) :
    A.IsSourceFullMixedGood P α β := by
  intro e
  exact
    A.sourceFullMixedGoodAtFace_of_not_mem_badBase
      P e (α e.rank) (β e.rank) (havoid e)

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
/-! ## Surviving tuples are source-full mixed-good -/
open Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration

open Wikipedia.SzemeredisTheorem.ClosedOrderedAtomConfiguration in
/-- If a full tuple avoids every source-full top deletion, its canonical
coarse closed atom configuration is source-full mixed-good at every positive
face. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (hrk : r ≤ k)
    (P : OrderedCoarseFineComplex G k r)
    (x : Fin k → G) (α β : ℕ → ℝ)
    (havoid :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∉
          P.sourceFullTopBadBaseDeletion e α β) :
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).IsSourceFullMixedGood P α β := by
  apply
    (ClosedOrderedAtomConfiguration.ofTuple
      P.coarse x).isSourceFullMixedGood_of_avoids_badBases
      P α β
  intro f hbad
  obtain ⟨e, d, hde⟩ :=
    exists_orderedFace_factor_through
      (Nat.succ_le_iff.mpr f.lowerRank.2) hrk f.face
  apply havoid e
  rw [OrderedCoarseFineComplex.sourceFullTopBadBaseDeletion]
  apply Finset.mem_biUnion.mpr
  refine ⟨⟨f.lowerRank, d⟩, Finset.mem_univ _, ?_⟩
  rw [mem_orderedFacePullbackFinset]
  change
    orderedFaceTuple (d.trans e) x ∈
      P.sourceFullCoarseOwnAtomBadBaseSupport
        ({ lowerRank := f.lowerRank
           face := d.trans e } : PositiveOrderedFace k r)
        (α (f.lowerRank.1 + 1))
        (β (f.lowerRank.1 + 1))
  rw [hde]
  exact hbad
