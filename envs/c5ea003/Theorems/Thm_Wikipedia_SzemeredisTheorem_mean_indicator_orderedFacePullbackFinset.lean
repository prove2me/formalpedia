-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_indicator_orderedFacePullbackFinset
-- name    : Wikipedia.SzemeredisTheorem.mean_indicator_orderedFacePullbackFinset
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:15.895542+00:00
-- url     : https://prove2.me/theorems/d2ae0d16-0ecb-43d8-acfc-72846e464a12
-- title:
--   Ordered coordinate pullback preserves density
-- statement:
--   Let $G$ be a nonempty finite set, let $r,j$ be nonnegative integers, and let $d:\{0,\ldots,j-1\}\hookrightarrow\{0,\ldots,r-1\}$ be an increasing embedding. For $S\subseteq G^j$, write $\pi_d:G^r\to G^j$ for coordinate restriction along $d$. Then
--   $$
--   \mathbb E_{x\in G^r}1_{\pi_d^{-1}(S)}(x)=\mathbb E_{y\in G^j}1_S(y).
--   $$
--   Hence pulling a finite set back along an ordered coordinate face preserves its normalized density.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedRemoval.lean#L338-L363

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Finite union bounds -/
/-! ## The bad base attached to the tuple's own upper atom -/
/-! ## Ordered specialization -/
/-! ## Pullback to top faces -/

theorem Wikipedia.SzemeredisTheorem.mean_indicator_orderedFacePullbackFinset
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {r j : ℕ}
    (d : OrderedFace r j)
    (S : Finset (Fin j → G)) :
    mean (finsetIndicator
        (orderedFacePullbackFinset d S)) =
      mean (finsetIndicator S) := by sorry
