-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.partialConfigurationWeight_univ_eq_zero_of_not_occurrence
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:26:26.664621+00:00
-- url     : https://prove2.me/submissions/40f8be2c-cc1d-4693-b320-cc8e04bc7481

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_ClosedOrderedAtomConfiguration_edge_of_mem_topAtom

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Ordered pattern edge partitions

The top layer used in ordered removal must remember the original
hypergraph.  For every top face we therefore generate a two-cell partition
from its edge set.  Any later refinement of that layer has atoms which are
monochromatic for the original edge predicate.

The lower layers of `orderedPatternInitialComplex` are indiscrete.  This is
the canonical starting complex for the all-rank regularity argument.
-/

namespace Wikipedia.SzemeredisTheorem

/-! ## Edge supports and their two-cell partitions -/













/-! ## Canonical initial complex -/









/-! ## Closed configurations contained in the original pattern -/



/-- Every full tuple realizing all selected top atoms of an occurring
closed configuration is itself an occurrence of the original pattern. -/
theorem ClosedOrderedAtomConfiguration.isOccurrence_of_mem_topAtoms
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    {C : OrderedPartitionComplex G k r}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k r C)
    (hA : H.IsOccurrence A.witness)
    (x : Fin k → G)
    (hx :
      ∀ e : OrderedFace k r,
        orderedFaceTuple e x ∈
          (A.atom (Fin.last r) e).1) :
    H.IsOccurrence x := by
  intro e
  exact A.edge_of_mem_topAtom H hC hA e
    (orderedFaceTuple e x) (hx e)

end Wikipedia.SzemeredisTheorem

end
/-!
# The ordered removal cover contradiction

This file joins the three semantic parts of ordered hypergraph removal.

* The top partition remembers the original edge predicates.
* A tuple surviving every bad-base deletion determines a good closed fine
  atom configuration.
* The configuration counting lemma gives every good configuration a
  uniform lower count.

Every tuple counted by the selected configuration remains an occurrence of
the original pattern, because its selected top atoms are edge-monochromatic.
Thus an occurrence surviving all deletions would force the original pattern
count above the assumed small-count threshold.
-/
open Wikipedia.SzemeredisTheorem
/-! ## The selected configuration lies inside the original pattern -/

open Wikipedia.SzemeredisTheorem in
/-- If a full tuple is not an occurrence, then the full selected
configuration weight of an occurring closed configuration vanishes on that
tuple. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k n : ℕ}
    (H : OrderedPattern G k (n + 1))
    {C : OrderedPartitionComplex G k (n + 1)}
    (hC : OrderedFacePartitionRefines C.topLayer
      (orderedPatternTopPartition H))
    (A : ClosedOrderedAtomConfiguration G k (n + 1) C)
    (hA : H.IsOccurrence A.witness)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    partialConfigurationWeight A Finset.univ x = 0 := by
  have hmissing :
      ∃ e : OrderedFace k (n + 1),
        orderedFaceTuple e x ∉
          (A.atom (Fin.last (n + 1)) e).1 := by
    by_contra h
    push Not at h
    exact hx
      (A.isOccurrence_of_mem_topAtoms
        H hC hA x h)
  obtain ⟨e, he⟩ := hmissing
  unfold partialConfigurationWeight
  apply Finset.prod_eq_zero
    (Finset.mem_univ (topPositiveOrderedFace e))
  unfold configurationFaceWeight
  change
    partitionAtomIndicator
        (C.partition (Fin.last (n + 1)) e)
        (A.atom (Fin.last (n + 1)) e)
        (orderedFaceTuple e x) =
      0
  exact
    partitionAtomIndicator_of_not_mem
      (C.partition (Fin.last (n + 1)) e)
      (A.atom (Fin.last (n + 1)) e) he
