-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.coarse_boundary_mem_of_boundary_weight_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:35.81552+00:00
-- url     : https://prove2.me/submissions/2f666f68-b61c-4241-b9f8-5e3259bfe812

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
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
# Shared ordered-face partitions and boundary pullbacks

The hypergraph-complex regularity proof uses one genuine partition on every
ordered lower face.  If `e` is an upper face, its boundary partition is not
an independently generated partition of the whole upper tuple space.  It is
the common refinement of the pullbacks of the shared partitions on the
immediate subfaces `eraseOrderedFace e i`.

This file implements that architecture.  Its central membership theorem says
that two upper tuples lie in the same boundary atom exactly when every pair
of erased tuples lies in the same atom of the corresponding genuine lower
face partition.  This is the compatibility needed for closed atom
configurations and localized energy estimates.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators











namespace OrderedFacePartitionRefines





end OrderedFacePartitionRefines





































namespace OrderedPartitionComplex

/-- Extract a numerically indexed layer from a bounded partition complex. -/
def layer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (j : ℕ) (hj : j ≤ r) :
    OrderedFacePartitionSystem G k j :=
  C.partition ⟨j, Nat.lt_succ_iff.mpr hj⟩











end OrderedPartitionComplex

end Wikipedia.SzemeredisTheorem

end

section


/-!
# Good ordered atoms and localized bad-base accounting

The hypergraph removal argument must localize a global coarse--fine energy
gap to genuine boundary atoms.  This file supplies the finite bookkeeping
for that step.

For an arbitrary finite partition we define the union of a selected family
of atoms and prove that its normalized mass is the sum of the atom masses.
Sublevel atoms charge only a small part of a target atom, while atoms on
which a nonnegative local average is large satisfy a finite Markov bound.
Applying this to the square of a coarse--fine conditional-density defect
gives the headline estimate

```text
mass (upperAtom ∩ badBase) ≤
  densityThreshold + atomEnergyGap / defectThreshold.
```

The final section specializes these definitions to shared ordered
boundaries and packages realizable closed atom configurations.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Canonical atoms and unions of genuine partition atoms -/































/-! ## Sublevel atoms and low-density charging -/









/-! ## Large local averages and finite Markov bounds -/











/-! ## Coarse--fine defect bases -/

























/-! ## Ordered boundary specialization -/



























/-! ## Good local configurations and closed atom configurations -/









namespace ClosedOrderedAtomConfiguration



/-- Every atom of a realizable closed configuration is the canonical atom
of its witness. -/
theorem atom_eq_partitionAtomAt
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (j : Fin (r + 1)) (e : OrderedFace k j.1) :
    A.atom j e =
      partitionAtomAt (C.partition j e)
        (orderedFaceTuple e A.witness) := by
  apply Subtype.ext
  exact
    ((C.partition j e).part_eq_of_mem
      (A.atom j e).2 (A.mem_atom j e)).symm









end ClosedOrderedAtomConfiguration

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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Positive-rank faces and immediate downward closure -/
/-! ## Missing coordinates for lower-or-equal rank faces -/
/-! ## Selected atom weights and counts -/
/-! ## Freezing and grouping a maximum-rank remainder -/
/-! ## Coarse densities, defects, and boundary support -/

open Wikipedia.SzemeredisTheorem in
/-- A nonzero selected factor on an immediate positive boundary face puts
the erased tuple in the corresponding coarse boundary atom. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.fine)
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1))
    (x : Fin k → G)
    (hweight :
      configurationFaceWeight A (e.boundary hpos i)
          (orderedFaceTuple (e.boundary hpos i).face x) ≠
        0) :
    eraseBoundaryCoordinate i (orderedFaceTuple e.face x) ∈
      (positiveFaceLowerLayer P.coarse e
        (eraseBoundaryFace e.face i)).part
        (eraseBoundaryCoordinate i
          (orderedFaceTuple e.face A.witness)) := by
  rcases e with ⟨⟨n, hn⟩, eface⟩
  cases n with
  | zero =>
      simp at hpos
  | succ n =>
      let f :=
        (⟨⟨n, by omega⟩,
            eraseBoundaryFace eface i⟩ :
          PositiveOrderedFace k r)
      have hfine :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hweight
          (partitionAtomIndicator_of_not_mem
            (P.fine.partition f.lowerRank.succ f.face)
            (A.atom f.lowerRank.succ f.face) hnot)
      have hcanonical :
          (A.atom f.lowerRank.succ f.face).1 =
            (P.fine.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) := by
        exact congrArg Subtype.val
          (A.atom_eq_partitionAtomAt
            f.lowerRank.succ f.face)
      rw [hcanonical] at hfine
      have hcoarse :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition f.lowerRank.succ f.face).part
              (orderedFaceTuple f.face A.witness) :=
        FacePartition.part_subset_of_le
          (P.refines f.lowerRank.succ f.face)
          (orderedFaceTuple f.face A.witness) hfine
      let j : Fin (r + 1) :=
        ⟨n + 1, Nat.lt_succ_of_lt hn⟩
      have hfj : f.lowerRank.succ = j := by
        apply Fin.ext
        rfl
      have hcoarse' :
          orderedFaceTuple f.face x ∈
            (P.coarse.partition j f.face).part
              (orderedFaceTuple f.face A.witness) := by
        subst j
        exact hcoarse
      simpa [f, j, positiveFaceLowerLayer,
        OrderedPartitionComplex.layer] using hcoarse'
