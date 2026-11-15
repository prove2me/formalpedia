-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_OrderedCoarseFineComplex_mean_indicator_sourceFullOwnAtomBadBaseSupport_le
-- name    : Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:35:13.389629+00:00
-- url     : https://prove2.me/theorems/f67cac6b-4830-4d61-995d-0b417d1b3339
-- title:
--   The source-full own-atom cleaning estimate
-- statement:
--   Let $G$ be finite and nonempty with decidable equality, $P$ an ordered coarse-fine complex, $e$ a positive ordered face, and $U$ an upper partition. For $\alpha\ge0$ and $\beta>0$, the normalized density of the source-full own-atom bad-base support is at most $\operatorname{complexity}(U)\alpha$ plus the difference between the fine and coarse lower-layer atom energies relative to $e,U$, divided by $\beta$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/SourceFullGoodAtoms.lean#L339-L393

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex
/-! ## Full-lower large-defect supports -/
/-! ## Low-density union and own-atom accounting -/

theorem Wikipedia.SzemeredisTheorem.OrderedCoarseFineComplex.mean_indicator_sourceFullOwnAtomBadBaseSupport_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (e : PositiveOrderedFace k r)
    (upper : FacePartition (Fin (e.lowerRank.1 + 1) → G))
    {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    mean (finsetIndicator
        (P.sourceFullOwnAtomBadBaseSupport
          e upper α β)) ≤
      (FacePartition.complexity upper : ℝ) * α +
        (orderedAtomEnergy
            (positiveFaceLowerLayer P.fine e) e.face upper -
          orderedAtomEnergy
            (positiveFaceLowerLayer P.coarse e) e.face upper) / β := by sorry
