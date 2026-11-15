-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mixedConfigurationDefect_mul_boundaryIndicator
-- name    : Wikipedia.SzemeredisTheorem.mixedConfigurationDefect_mul_boundaryIndicator
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:29.527485+00:00
-- url     : https://prove2.me/theorems/51c7e91a-1fe7-482a-8532-e6a6f54a1401
-- title:
--   Mixed and ordinary defects agree on the coarse boundary atom
-- statement:
--   Let $G$ be finite, let $k,r$ be natural numbers, let $P$ be an ordered coarse–fine complex, and let $A$ be a closed ordered atom configuration for its coarse complex. Fix a positive ordered face $e$ and a tuple $y$ on its lower-rank successor face. Write $D_{P,A,e}$ for the mixed configuration defect and $B_{P,A,e}$ for its canonical coarse boundary indicator. Then
--   $$
--   D_{P,A,e}(y)B_{P,A,e}(y)=\Delta_{P,A,e}(y)B_{P,A,e}(y),
--   $$
--   where $\Delta_{P,A,e}$ is the ordinary fine-minus-coarse boundary defect of the selected coarse upper atom, using the fine and coarse positive-face lower layers.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/CoarseConfigurationCounting.lean#L449-L504

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
# Positive counts for mixed-good coarse configurations

A closed configuration in this file selects atoms of the coarse complex.
The selected coarse upper atom is decomposed using conditional expectation
first on the fine lower boundary and then on the coarse lower boundary.
Thus the main density and defect are exactly those controlled by
`ClosedOrderedAtomConfiguration.IsMixedGood`, while the uniform term is
controlled by regularity of the fine lower boundary against the coarse upper
partition.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## A diagonal pair used only for coarse boundary support -/
/-! ## Mixed coarse/fine conditional decomposition -/
/-! ## Coarse boundary support and selected-face decomposition -/
/-! ## Mixed coarse-upper regularity and the uniform contribution -/
/-! ## Localized mixed defect contribution -/

theorem Wikipedia.SzemeredisTheorem.mixedConfigurationDefect_mul_boundaryIndicator
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    mixedConfigurationDefect P A e y *
        mixedConfigurationBoundaryIndicator P A e y =
      orderedAtomBoundaryDefect
          (positiveFaceLowerLayer P.fine e)
          (positiveFaceLowerLayer P.coarse e)
          e.face
          (P.coarse.partition e.lowerRank.succ e.face)
          (A.atom e.lowerRank.succ e.face) y *
        mixedConfigurationBoundaryIndicator P A e y := by sorry
