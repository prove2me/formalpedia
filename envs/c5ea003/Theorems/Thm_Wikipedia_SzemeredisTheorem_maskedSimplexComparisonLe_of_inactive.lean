-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_maskedSimplexComparisonLe_of_inactive
-- name    : Wikipedia.SzemeredisTheorem.maskedSimplexComparisonLe_of_inactive
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:10.200609+00:00
-- url     : https://prove2.me/theorems/02bb466e-e120-40ce-b702-fdaceb78df25
-- title:
--   Inactive-mask simplex comparison
-- statement:
--   Let $n\ge0$ and $N\ge1$ be integers, let $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$, and let $c\in\mathbb R$. Suppose every face is inactive. For any two weighted simplex systems $H,K$, if $H$ is majorized by the canonical AP masked majorant, $K$ has edge weights in $[0,1]$, and their edge-face cut discrepancy is at most $c$, then
--   $$
--   \lvert\operatorname{count}(H)-\operatorname{count}(K)\rvert\le(n+1)c.
--   $$
--   Equivalently the masked comparison property holds with cut error $c$ and count error $(n+1)c$. This is the empty-active-mask induction base.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingInduction.lean#L501-L524

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ConvolutionMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_GeneralRelativeSimplexStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedFaceCutClosure
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingCertificate
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoder
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderStep
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingDecoderTerminal
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
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
# Active-majorant recurrence for relative simplex counting

The weighted Cauchy--Schwarz decoder supplies a certificate when both
copies of every active incident face use the same AP majorant.  Relative
counting also produces two cross terms: one omitted-coordinate copy is
sparse and the other is bounded by one.  This file separates those two
issues exactly.

First, the completed homogeneous certificate is transported from AP
pullback factors to arbitrary weighted-simplex edge factors.  This is
possible because a `HasCFZCertificate` depends on the core and designated
majorants, but not on the particular nonnegative factors below them.

The second part packages the active-cardinality bookkeeping and the
one-step counting recurrence.  Its only extra strong-linear-forms input is
the pair of genuinely mixed-copy centered correlations.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Factor-independence of structural CFZ certificates -/
/-! ## Arbitrary simplex factors under homogeneous AP majorants -/
/-! ## Active-face cardinality and the comparison invariant -/

theorem Wikipedia.SzemeredisTheorem.maskedSimplexComparisonLe_of_inactive
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (hactive : ∀ i, active i = false)
    (cutError : ℝ) :
    MaskedSimplexComparisonLe n N ν active
      cutError (((n + 1 : ℕ) : ℝ) * cutError) := by sorry
