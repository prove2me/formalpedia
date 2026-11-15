-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:04:12.091243+00:00
-- url     : https://prove2.me/theorems/4a7a625e-2259-4607-9455-470e6dbacbd0
-- title:
--   Layer operations and compatible coarse/fine ordered complexes
-- statement:
--   For an ordered partition complex of bounded rank, the bundle supplies its top layer, the complex obtained by dropping the top layer, the operation of appending a new top layer, and replacement of only the existing top layer.
--
--   A compatible coarse/fine pair records two complexes together with pointwise refinement of the fine complex over the coarse one at every rank and ordered face. A regularity-tolerance family assigns one real tolerance to each adjacent rank pair. These are the structural interfaces used when assembling one-layer regularity constructions across the whole ordered complex.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/FullOrderedRegularity.lean#L29-L393

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Lean
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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace OrderedPartitionComplex

/-- The top shared-face layer of a bounded ordered partition complex. -/
def topLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r) :
    OrderedFacePartitionSystem G k r :=
  C.partition (Fin.last r)

/-- Forget the top layer of a nontrivial ordered partition complex. -/
def dropTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k (r + 1)) :
    OrderedPartitionComplex G k r where
  partition j := C.partition j.castSucc

/-- Append one new top layer to an ordered partition complex. -/
def appendTop
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k (r + 1)) :
    OrderedPartitionComplex G k (r + 1) where
  partition j :=
    Fin.lastCases top (fun i => C.partition i) j

/-- Replace only the top layer of an ordered partition complex. -/
def withTopLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (top : OrderedFacePartitionSystem G k r) :
    OrderedPartitionComplex G k r where
  partition j :=
    Fin.lastCases top (fun i => C.partition i.castSucc) j























end OrderedPartitionComplex

/-! ## Coarse/fine complexes and honest atom-energy gaps -/

/-- A pair of compatible ordered partition complexes, with the fine complex
refining the coarse one at every genuine face. -/
structure OrderedCoarseFineComplex
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) where
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse

namespace OrderedCoarseFineComplex



























end OrderedCoarseFineComplex

/-! ## Rank schedules and simultaneous preliminary regularity -/

/-- One tolerance for every adjacent rank pair `(j, j + 1)`. -/
abbrev OrderedRegularityTolerance (r : ℕ) := Fin r → ℝ











/-! ## The top-down all-rank construction -/







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.ctorIdx,
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.mk.inj,
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.mk.injEq,
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.noConfusionType,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.appendTop.eq_1,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.dropTop.eq_1,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.topLayer.eq_1,
    `Wikipedia.SzemeredisTheorem.OrderedPartitionComplex.withTopLayer.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


