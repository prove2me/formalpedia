-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
-- name    : Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:29:23.737993+00:00
-- url     : https://prove2.me/theorems/3d683a32-ec6f-487b-9517-13ec9d80894a
-- title:
--   Mixed-copy correlation bound with a sparse first copy
-- statement:
--   Let $N\ne0$, assume the $(m+2)$-linear-forms condition for a nonnegative function $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$ with error $\eta$, and fix an active-face mask and face $j$. Suppose the first simplex system $H$ has nonnegative weights below the masked AP majorant and the second $K$ has weights in $[0,1]$. For $\varepsilon\ge0$, if $(1+\eta)^{2^{m+1}-1}2^{|\mathrm{DeletedCube}(m+2,j)|}\eta\le\varepsilon^{2^{m+1}}$, the absolute heterogeneous two-copy centered correlation of $(H,K)$ at $j$ is at most $\varepsilon$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingHeterogeneousMask.lean#L1560-L1601

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
# Copy-dependent masks in relative counting

The two copies in a projected relative-counting correlation need not have
the same majorant.  This file allows a separate active-face mask

`active : Bool → Fin (n + 1) → Bool`

for each copy.  The corresponding Cauchy--Schwarz stage selector reads the
copy from the distinguished Boolean coordinate of a face vertex.  Thus a
face can retain the `false` copy of `ν`, the `true` copy, both copies, or
neither copy independently.

The stable stage and terminal decoders then give a full structural CFZ
certificate and the usual quantitative root bound.  The final specialization
uses `ν` on the `false` copy and the constant majorant one on the `true`
copy, which is the cross-copy case required by relative counting.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## The copy-dependent AP cut system -/
/-! ## Copy-aware recursive stage selectors -/
/-! ## Copy-aware paid stage moments -/
/-! ## Copy-aware terminal selector -/
/-! ## Quantitative correlation bounds -/
/-! ## Arbitrary weighted-simplex factors -/
/-! ## Arbitrary-factor quantitative bridge -/

theorem Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_heterogeneousMaskSimplexTwoCopyCenteredCorrelation_le_of_falseSparse_trueDense
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η ε : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (active : Fin (m + 2) → Bool)
    (H K : WeightedSimplexSystem
      (fun _ : Fin (m + 2) => ZMod N))
    (j : Fin (m + 2))
    (hH :
      ∀ i x,
        0 ≤ H.edgeWeight i x ∧
          H.edgeWeight i x ≤
            (apHeterogeneousSimplexSystem (m + 1) N
              (apMaskedFaceMajorant ν active)).edgeWeight i x)
    (hK : EdgeWeightsInUnitInterval K)
    (hε : 0 ≤ ε)
    (hconvert :
      (1 + η) ^ (2 ^ (m + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (m + 2) j) * η) ≤
        ε ^ (2 ^ (m + 1))) :
    |heterogeneousMaskSimplexTwoCopyCenteredCorrelation
        (m + 1) N ν
          (heterogeneousMaskSimplexCopyPair H K) j| ≤ ε := by sorry
