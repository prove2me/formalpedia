-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_faceCutDifferenceCorrelation_apCanonicalEdge_eq_linearCutCorrelation
-- name    : Wikipedia.SzemeredisTheorem.faceCutDifferenceCorrelation_apCanonicalEdge_eq_linearCutCorrelation
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:05.850052+00:00
-- url     : https://prove2.me/theorems/63abde9b-b2b4-44fa-b30c-650ceaca1791
-- title:
--   The AP edge correlation is a transported linear cut correlation
-- statement:
--   Let $N\ne0$ and assume $N$ is coprime to $n!$. For real functions $f,g$ on $\mathbb Z/N\mathbb Z$, a distinguished face $j$ of the length-$n+1$ AP simplex, and any arity-$n$ cut-test family $u$, the face-cut difference correlation of the canonical AP edge functions equals the linear cut correlation with the canonical coefficient-scaling automorphisms.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeSimplexComparison.lean#L270-L298

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
/-! ## Bridge from the existing AP cut discrepancy -/

theorem Wikipedia.SzemeredisTheorem.faceCutDifferenceCorrelation_apCanonicalEdge_eq_linearCutCorrelation
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial n))
    (f g : ZMod N → ℝ)
    (j : Fin (n + 1))
    (u : CutTestFamily (ZMod N) n) :
    faceCutDifferenceCorrelation
        (canonicalEdgeFunction
          (apSimplexSystem (n + 1) N f) j)
        (canonicalEdgeFunction
          (apSimplexSystem (n + 1) N g) j) u =
      linearCutCorrelation n
        (apFaceScalingEquiv hN j) f g u := by sorry
