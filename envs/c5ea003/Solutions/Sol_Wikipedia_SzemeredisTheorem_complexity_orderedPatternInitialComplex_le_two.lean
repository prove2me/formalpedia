-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.complexity_orderedPatternInitialComplex_le_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:46:57.026193+00:00
-- url     : https://prove2.me/submissions/66068e09-2a57-4bc7-a22a-982fe93c4277

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_FacePartition_complexity_indiscrete

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# All-rank ordered preliminary regularity

The preliminary energy increment acts on one adjacent pair of ranks: it
refines the shared rank-`j` partitions while keeping rank `j + 1` fixed.
This file assembles those refinements into one compatible partition complex.
The ranks are processed from top to bottom.  Consequently, once the pair
`(j, j + 1)` has been regularized, later steps only change lower ranks and
cannot invalidate it.

The resulting theorem has a separate tolerance and finite energy budget at
every adjacent pair.  It returns an explicit stopping-time schedule, a
refining complex which is preliminarily regular at every rank, and the
ambient-independent complexity multiplier at every non-top layer.

We also package coarse/fine complexes and their boundary atom-energy gap.
The gap uses the atoms of the fine upper layer at both endpoints; with that
choice, refinement of the lower boundary gives honest monotonicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedPartitionComplex













@[simp]
theorem topLayer_withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    (withTopLayer C top).topLayer = top := by
  simp [topLayer, withTopLayer]

















end OrderedPartitionComplex

/-! ## Coarse/fine complexes and honest atom-energy gaps -/



namespace OrderedCoarseFineComplex



























end OrderedCoarseFineComplex

/-! ## Rank schedules and simultaneous preliminary regularity -/













/-! ## The top-down all-rank construction -/







end Wikipedia.SzemeredisTheorem

end

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







/-- Every original edge/nonedge top partition has at most two atoms. -/
theorem complexity_orderedPatternTopPartition_le_two
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r)
    (e : OrderedFace k r) :
    FacePartition.complexity
        (orderedPatternTopPartition H e) ≤ 2 := by
  simpa [orderedPatternTopPartition] using
    FacePartition.complexity_generatedBy_le
      ({H.edgeFinset e} :
        Finset (Finset (Fin r → G)))





/-! ## Canonical initial complex -/





@[simp]
theorem orderedPatternInitialComplex_topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    (orderedPatternInitialComplex H).topLayer =
      orderedPatternTopPartition H := by
  exact OrderedPartitionComplex.topLayer_withTopLayer _ _



/-! ## Closed configurations contained in the original pattern -/





end Wikipedia.SzemeredisTheorem

end
/-!
# Schedule-level assembly of ordered hypergraph removal

The structural regularity theorem accepts a tolerance schedule, a
weak-regularity budget at every stage, and one energy-selection length at
every rank.  `OrderedRemovalParameters` identifies the two numerical
inequalities those schedules must satisfy.  This file performs all remaining
quantifier and semantic assembly.

The main theorem is deliberately conditional on the existence of compatible
ambient-independent schedules.  It proves that such schedules imply
`HasUniformOrderedPatternRemoval`; no fixed point or diagonal selector is
assumed to have been constructed here.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## The canonical pattern complex has complexity at most two -/

open Wikipedia.SzemeredisTheorem in
/-- Every layer of the canonical edge-monochromatic input complex has at
most two atoms.  Lower layers are indiscrete and the top layer is generated
by one edge predicate. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ} (H : OrderedPattern G k r) :
    ∀ (j : Fin (r + 1)) (e : OrderedFace k j.1),
      FacePartition.complexity
          ((orderedPatternInitialComplex H).partition j e) ≤ 2 := by
  intro j
  cases j using Fin.lastCases with
  | last =>
      intro e
      change
        FacePartition.complexity
            ((orderedPatternInitialComplex H).topLayer e) ≤ 2
      rw [orderedPatternInitialComplex_topLayer]
      exact complexity_orderedPatternTopPartition_le_two H e
  | cast i =>
      intro e
      simp [orderedPatternInitialComplex,
        indiscreteOrderedPartitionComplex,
        OrderedPartitionComplex.withTopLayer]
