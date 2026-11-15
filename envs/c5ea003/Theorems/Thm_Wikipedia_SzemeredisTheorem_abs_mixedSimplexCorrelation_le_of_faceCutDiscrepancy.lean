-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_mixedSimplexCorrelation_le_of_faceCutDiscrepancy
-- name    : Wikipedia.SzemeredisTheorem.abs_mixedSimplexCorrelation_le_of_faceCutDiscrepancy
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:44.482517+00:00
-- url     : https://prove2.me/theorems/447aefc1-5908-45f4-98ab-aaca8ec74ea5
-- title:
--   Face-cut discrepancy bounds a mixed simplex correlation
-- statement:
--   Let $G$ be finite and nonempty and let $H,K$ be weighted simplex systems on $n+1$ copies of $G$ with edge weights in $[0,1]$. If the canonical edge functions of a distinguished face $j$ have face-cut discrepancy at most $\varepsilon$, then their mixed simplex correlation at $j$ has absolute value at most $\varepsilon$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeSimplexComparison.lean#L199-L234

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
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
# Cut-discrepancy comparison of bounded relative simplex states

For an arbitrary simplex edge, the natural discrepancy is tested directly
on its deleted-face coordinates against products of functions omitting one
face coordinate.  This is the same cut-test family used by
`FaceRegularityState.IsFaceCutRegular`, but here it compares two arbitrary
edge functions rather than a function and its conditional expectation.

The existing `simplexMixedCutTest` reconstructs the product of all
non-distinguished factors in an edge-by-edge telescoping term.  Consequently
face-cut discrepancy controls each mixed correlation whenever both simplex
systems are fully bounded.  Summing the correlations gives an actual
weighted-simplex comparison theorem with loss one `ε` per colour.

The final section specializes this comparison to the arbitrary whole-face
functions produced by recursive projection and re-embedding.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Direct face-cut discrepancy -/
/-! ## Edgewise discrepancy for arbitrary weighted simplices -/

theorem Wikipedia.SzemeredisTheorem.abs_mixedSimplexCorrelation_le_of_faceCutDiscrepancy
    {G : Type*} [Fintype G] [Nonempty G]
    {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1))
    {ε : ℝ}
    (hcut :
      FaceCutDiscrepancyLe
        (canonicalEdgeFunction H j)
        (canonicalEdgeFunction K j) ε) :
    |mixedSimplexCorrelation H K j| ≤ ε := by sorry
