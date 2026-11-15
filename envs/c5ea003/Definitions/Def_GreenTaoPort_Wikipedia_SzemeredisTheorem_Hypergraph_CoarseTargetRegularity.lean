-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:36.001163+00:00
-- url     : https://prove2.me/theorems/52743b74-be9b-4f23-ad8c-3a2673dbfba6
-- title:
--   A coarse-upper-target ordered regularity certificate
-- statement:
--   Given an initial ordered partition complex, rankwise tolerance and budget schedules, and finite search lengths, this structure records compatible coarse and fine complexes together with a selected index at each lower rank. The coarse complex refines the initial one, the fine complex refines the coarse one, and both retain the initial top layer.
--
--   At each rank, the fine lower boundary is preliminarily regular against the final coarse upper layer. The certificate includes a nonnegative energy gap bounded by the number of ordered upper faces divided by the search length, plus explicit coarse and fine complexity bounds at the selected index and its successor. A projection forgets these quantitative certificates and retains the coarse/fine pair.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseTargetRegularity.lean#L24-L103

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Lean
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


/-!
# Strong ordered regularity with coarse upper targets

The usual top-down strong certificate freezes the final fine upper layer
while selecting the adjacent coarse/fine lower layers.  For coarse
configuration counting and cleaning, the more useful target is instead the
final coarse upper layer.

This file carries out that variant directly.  At the current top rank we
select a coarse/fine lower pair against the unchanged top layer.  The
recursive call is then made with the selected *coarse* lower layer as its
top layer.  After recursion, only the fine prefix's top layer is replaced
by the selected fine layer.  Thus every lower-rank regularity statement and
energy gap keeps the recursively selected coarse upper layer as its target.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A top-down strong regularity certificate in which the observing fine
lower boundary is regular against the final coarse upper layer, and the
rankwise energy gap is measured against that same coarse upper layer. -/
structure CoarseTargetOrderedComplexRegularityCertificate
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ)
    (initial : OrderedPartitionComplex G k r)
    (ε : (j : Fin r) → ℕ → ℝ)
    (budget : (j : Fin r) → ℕ → ℕ)
    (length : Fin r → ℕ) where
  index : Fin r → ℕ
  coarse : OrderedPartitionComplex G k r
  fine : OrderedPartitionComplex G k r
  refines : fine.Refines coarse
  coarse_refines_initial : coarse.Refines initial
  coarse_topLayer_eq :
    coarse.topLayer = initial.topLayer
  fine_topLayer_eq :
    fine.topLayer = initial.topLayer
  index_lt : ∀ j, index j < length j
  mixedRegular :
    ∀ j : Fin r,
      IsPreliminaryOrderedRegular
        (fine.partition j.castSucc)
        (coarse.partition j.succ)
        (ε j (index j))
  gap_nonneg :
    ∀ j : Fin r,
      0 ≤
        orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ)
  gap_le :
    ∀ j : Fin r,
      orderedLayerAtomEnergy
            (fine.partition j.castSucc)
            (coarse.partition j.succ) -
          orderedLayerAtomEnergy
            (coarse.partition j.castSucc)
            (coarse.partition j.succ) ≤
        (Fintype.card
          (OrderedFace k (j.1 + 1)) : ℝ) /
            (length j : ℝ)
  coarse_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (coarse.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j) *
          FacePartition.complexity
            (initial.partition j.castSucc e)
  fine_complexity :
    ∀ (j : Fin r) (e : OrderedFace k j.1),
      FacePartition.complexity
          (fine.partition j.castSucc e) ≤
        fixedUpperLayerComplexityFactor
            j.1 (budget j) (index j + 1) *
          FacePartition.complexity
            (initial.partition j.castSucc e)

namespace CoarseTargetOrderedComplexRegularityCertificate

/-- Forget the quantitative certificate and retain its compatible
coarse/fine complexes. -/
def toCoarseFine
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {initial : OrderedPartitionComplex G k r}
    {ε : (j : Fin r) → ℕ → ℝ}
    {budget : (j : Fin r) → ℕ → ℕ}
    {length : Fin r → ℕ}
    (R : CoarseTargetOrderedComplexRegularityCertificate
      G k r initial ε budget length) :
    OrderedCoarseFineComplex G k r where
  coarse := R.coarse
  fine := R.fine
  refines := R.refines



end CoarseTargetOrderedComplexRegularityCertificate

/-! ## Existence by downward rank induction -/



/-! ## Total coarse-target gap -/

namespace OrderedCoarseFineComplex





end OrderedCoarseFineComplex

namespace CoarseTargetOrderedComplexRegularityCertificate





end CoarseTargetOrderedComplexRegularityCertificate



end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.CoarseTargetOrderedComplexRegularityCertificate.ctorIdx,
    `Wikipedia.SzemeredisTheorem.CoarseTargetOrderedComplexRegularityCertificate.mk.inj,
    `Wikipedia.SzemeredisTheorem.CoarseTargetOrderedComplexRegularityCertificate.mk.injEq,
    `Wikipedia.SzemeredisTheorem.CoarseTargetOrderedComplexRegularityCertificate.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.CoarseTargetOrderedComplexRegularityCertificate.noConfusionType
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


