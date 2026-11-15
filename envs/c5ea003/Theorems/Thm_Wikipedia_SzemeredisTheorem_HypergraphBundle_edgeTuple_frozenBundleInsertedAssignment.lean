-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_edgeTuple_frozenBundleInsertedAssignment
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.edgeTuple_frozenBundleInsertedAssignment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:22.314602+00:00
-- url     : https://prove2.me/theorems/57cf3084-3715-47c1-9564-6258218a415d
-- title:
--   Inserting the missing coordinate preserves another edge tuple
-- statement:
--   Let $B$ be a finite hypergraph bundle over the ordered configuration base edges. Choose a nonempty edge $g_0$ of maximal cardinality and another edge $g\ne g_0$. For any value type $G$, frozen value $a$, local tuple $x$, and outside assignment $z$, insertion of $a$ at the missing coordinate assigned to $g$ leaves the tuple seen by $g$ equal to the tuple obtained from the original local assignment and $z$. The statement requires no finiteness or decidable equality on $G$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleFrozenCut.lean#L245-L305

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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleConfigurationStep
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFrozenUniformity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleRelativeCounting
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
# Frozen bundle remainders are face cuts

Fix a maximum-cardinality nonempty occurrence edge `g₀`.  Every other
occurrence edge omits a vertex of `g₀`; we assign that edge to the
corresponding coordinate in the increasing enumeration of the projected
edge.  After the variables outside `g₀` are frozen, factors with the same
assigned coordinate form one member of a face-cut family.

The construction groups *occurrence* edges, rather than projected faces.
This is important because distinct occurrence edges in a bundle may have
the same projection.  The resulting product therefore retains every
factor with its correct multiplicity.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}
/-! ## The canonical occurrence-edge ordering -/
/-! ## Assigning each remainder edge to a missing coordinate -/
/-! ## Reconstructing and grouping a frozen remainder -/

omit [Fintype G] [DecidableEq G] in

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.edgeTuple_frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G)
    (z : EdgeComplement g₀ → G) :
    edgeTuple g
        (B.frozenBundleInsertedAssignment hg₀ hne
          (B.frozenBundleMissingCoordinate hg₀ hmax hne g)
          a
          (Fin.removeNth
            (B.frozenBundleMissingCoordinate hg₀ hmax hne g) x)
          z) =
      edgeTuple g
        ((splitEdgeEquiv g₀).symm
          ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z)) := by sorry
