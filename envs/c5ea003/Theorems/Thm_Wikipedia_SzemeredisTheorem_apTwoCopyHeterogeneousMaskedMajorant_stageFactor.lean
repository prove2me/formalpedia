-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_apTwoCopyHeterogeneousMaskedMajorant_stageFactor
-- name    : Wikipedia.SzemeredisTheorem.apTwoCopyHeterogeneousMaskedMajorant_stageFactor
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:42:03.695846+00:00
-- url     : https://prove2.me/theorems/997480cc-9491-45e1-a09e-49106f618bc9
-- title:
--   A heterogeneous stage majorant is the product of its two copy factors
-- statement:
--   Fix a Cauchy–Schwarz stage with $r$ processed and $s$ future coordinates over modulus $N$, a real majorant $\nu$, independent masks and AP weight families for both Boolean copies, and distinguished face $j$. Assume the untouched-face domination bounds for each copy. Evaluating the original current-coordinate majorant at the decoded stage input equals the product, over the two new Boolean choices, of that copy’s masked majorant evaluated at the corresponding current-face CFZ form.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RelativeCountingHeterogeneousMask.lean#L255-L373

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

theorem Wikipedia.SzemeredisTheorem.apTwoCopyHeterogeneousMaskedMajorant_stageFactor
    (r s N : ℕ)
    (ν : ZMod N → ℝ)
    (active :
      Bool → Fin (((s + 1) + r) + 1) → Bool)
    (g : Bool →
      APFaceWeightFamily ((s + 1) + r) N)
    (j : Fin (((s + 1) + r) + 1))
    (hrest :
      ∀ b,
        APUntouchedFaceBounds (g b)
          (apCopyMaskedFaceMajorant ν active b) j)
    (x : CubePoint (((s + 1) + r) + 1) N)
    (bits : Fin r → Bool) :
    (apTwoCopyHeterogeneousMaskedMajorizedCutSystem
        ((s + 1) + r) N ν active g j hrest).majorant
        (apCSOrderedStageCubeEquiv r s N j x).1.1.base
        (csOrderedStageCurrentIndex r s)
        (csOrderedStageFactorInput r s
          (fun i =>
            selectPair
              ((apCSOrderedStageCubeEquiv
                r s N j x).1.1.pair i)
              (bits i))
          (apCSOrderedStageCubeEquiv
            r s N j x).1.2) =
      ∏ b : Bool,
        apCopyMaskedFaceMajorant ν active b
          (apCSOrderedStageCurrentFace r s j)
          (apLinearForm (((s + 1) + r) + 1) N
            (apCSOrderedStageCurrentFace r s j)
            (apCSOrderedStageVertex r s j
              (Fin.cons b bits)) x) := by sorry
