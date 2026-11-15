-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.appendTop_refines
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:41:19.118209+00:00
-- url     : https://prove2.me/submissions/0379c8b8-1ba2-4c17-9647-9684e44f5d6a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.OrderedPartitionComplex

open Wikipedia.SzemeredisTheorem.OrderedPartitionComplex in
/-- Appending pointwise-refining top and lower layers preserves refinement
of the whole complex. -/
theorem solution
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {fine coarse : OrderedPartitionComplex G k r}
    {fineTop coarseTop :
      OrderedFacePartitionSystem G k (r + 1)}
    (hfc : fine.Refines coarse)
    (htop : OrderedFacePartitionRefines fineTop coarseTop) :
    (appendTop fine fineTop).Refines
      (appendTop coarse coarseTop) := by
  intro j e
  cases j using Fin.lastCases with
  | last =>
      simp only [appendTop, Fin.lastCases_last]
      change OrderedFace k (r + 1) at e
      change fineTop e ≤ coarseTop e
      exact htop e
  | cast i =>
      simp only [appendTop, Fin.lastCases_castSucc]
      change OrderedFace k i.1 at e
      change fine.partition i e ≤ coarse.partition i e
      exact hfc i e
