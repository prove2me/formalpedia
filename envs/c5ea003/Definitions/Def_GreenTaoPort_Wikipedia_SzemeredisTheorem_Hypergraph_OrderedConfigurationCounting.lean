-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:05:04.487372+00:00
-- url     : https://prove2.me/theorems/1d8891b1-1e0a-44ec-9f3c-cb0118e2e113
-- title:
--   Positive ordered faces and partial closed-configuration counts
-- statement:
--   A positive face of a complex of ranks zero through $r$ records a lower-rank index $j<r$ and an ordered face of actual arity $j+1$. The bundle gives its finite dependent-sum presentation, its actual rank, and its immediate positive boundary faces when the rank is at least two.
--
--   A closed atom configuration assigns a zero–one atom indicator to every positive face. For a finite subfamily, the partial configuration weight multiplies these indicators at the corresponding restrictions of a full tuple. Its normalized mean is the partial count; using all positive faces gives the full count. The canonical lower layer attached to a positive face is supplied with its rank normalized to the required tuple arity.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedConfigurationCounting.lean#L38-L655

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
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

/-- A positive-rank ordered face of a complex with ranks `0, ..., r`.
`lowerRank = j` represents an actual face of rank `j + 1`. -/
structure PositiveOrderedFace (k r : ℕ) where
  lowerRank : Fin r
  face : OrderedFace k (lowerRank.1 + 1)
deriving DecidableEq

namespace PositiveOrderedFace

/-- Positive ordered faces are the dependent sum of their rank index and
their increasing face. -/
def equivSigma (k r : ℕ) :
    PositiveOrderedFace k r ≃
      Σ j : Fin r, OrderedFace k (j.1 + 1) where
  toFun e := ⟨e.lowerRank, e.face⟩
  invFun e := ⟨e.1, e.2⟩
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

noncomputable instance instFintype (k r : ℕ) :
    Fintype (PositiveOrderedFace k r) :=
  Fintype.ofEquiv
    (Σ j : Fin r, OrderedFace k (j.1 + 1))
    (equivSigma k r).symm

/-- Actual cardinality/rank of a positive ordered face. -/
def rank {k r : ℕ} (e : PositiveOrderedFace k r) : ℕ :=
  e.lowerRank.1 + 1



/-- A positive immediate boundary face, obtained by erasing one coordinate.
The positivity hypothesis says that the original face has rank at least
two. -/
noncomputable def boundary
    {k r : ℕ}
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨e.lowerRank.1 - 1,
      lt_of_le_of_lt (Nat.sub_le _ _) e.lowerRank.2⟩
  refine ⟨j, ?_⟩
  have hj : j.1 + 1 = e.lowerRank.1 := by
    simp only [j]
    omega
  exact hj ▸ eraseBoundaryFace e.face i







end PositiveOrderedFace











/-! ## Missing coordinates for lower-or-equal rank faces -/











/-! ## Selected atom weights and counts -/

/-- Indicator of the atom selected by a closed configuration at one
positive-rank face. -/
def configurationFaceWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) : ℝ :=
  partitionAtomIndicator
    (C.partition e.lowerRank.succ e.face)
    (A.atom e.lowerRank.succ e.face) y





/-- Product of the selected atom indicators over a partial positive-face
family. -/
noncomputable def partialConfigurationWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r))
    (x : Fin k → G) : ℝ :=
  ∏ e ∈ s,
    configurationFaceWeight A e
      (orderedFaceTuple e.face x)

/-- Normalized count of one partial closed atom configuration. -/
noncomputable def partialConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (s : Finset (PositiveOrderedFace k r)) : ℝ :=
  mean (partialConfigurationWeight A s)

/-- Full normalized count of the selected positive-rank atoms. -/
noncomputable def fullConfigurationCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) : ℝ :=
  partialConfigurationCount A Finset.univ









/-! ## Freezing and grouping a maximum-rank remainder -/













/-! ## Coarse densities, defects, and boundary support -/

/-- Rank-normalized lower layer attached to a positive face. -/
def positiveFaceLowerLayer
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (C : OrderedPartitionComplex G k r)
    (e : PositiveOrderedFace k r) :
    OrderedFacePartitionSystem G k e.lowerRank.1 :=
  C.partition e.lowerRank.castSucc

























/-! ## Selected-face contributions and exact decomposition -/











/-! ## Uniform contribution -/





/-! ## Localized defect contribution -/















/-! ## The one-face recurrence -/













/-! ## Quantitative full-count lower bound and positivity -/





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.boundary.congr_simp,
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.ctorIdx,
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.mk.inj,
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.mk.injEq,
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.mk.sizeOf_spec,
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.noConfusionType,
    `Wikipedia.SzemeredisTheorem.PositiveOrderedFace.rank.eq_1,
    `Wikipedia.SzemeredisTheorem.instDecidableEqPositiveOrderedFace.decEq.match_1,
    `Wikipedia.SzemeredisTheorem.partialConfigurationCount.eq_1,
    `Wikipedia.SzemeredisTheorem.partialConfigurationWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.positiveFaceLowerLayer.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


