-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.apCSOrderedStageCubeEquiv_processedPair
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:29.540263+00:00
-- url     : https://prove2.me/submissions/d0909759-6405-4e86-9531-3278a008a560

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

section


/-!
# Stage decoders for relative-counting Cauchy--Schwarz recursion

Repeated applications of `MajorizedCutSystem.next` replace an external
parameter `P` by the left-associated tower

`(((P × (G × G)) × (G × G)) × ⋯)`.

The declarations below give this tower a stable stage-indexed name and
identify it with a base parameter together with a Boolean pair for every
coordinate already eliminated.  In the AP application the base parameter
is itself a Boolean pair, belonging to the distinguished omitted face.
Thus stage `r` is canonically a Boolean cube on `r + 1` axes.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## The nested parameter tower -/





















/-! ## Boolean-axis form of the AP parameter -/







/-! ## Full AP cube decoder -/









@[simp]
theorem apCSStageCubeEquiv_processedPair
    (r s N : ℕ)
    (j : Fin ((r + (s + 1)) + 1))
    (x : CubePoint ((r + (s + 1)) + 1) N)
    (i : Fin r) :
    (apCSStageCubeEquiv r s N j x).1.1.pair i =
      (x (j.succAbove (Fin.castAdd (s + 1) i)) false,
        x (j.succAbove (Fin.castAdd (s + 1) i)) true) := by
  simp [apCSStageCubeEquiv, apProjectionAxesEquiv,
    csStageDeletedAxesEquiv, CSStageParam.pair,
    boolEndpointEquiv]







/-! ## Expected CFZ selectors at a decoded stage -/













/-! ## Iterating `MajorizedCutSystem.next` -/

namespace MajorizedCutSystem



































end MajorizedCutSystem

/-! ## Quantitative endpoint after the decoded first stage -/



end Wikipedia.SzemeredisTheorem

end

section


/-!
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Prefixing the processed endpoint choices -/



































/-! ## Closed formula for an iterated designated majorant -/

namespace MajorizedCutSystem





end MajorizedCutSystem

/-! ## The selected stage vertices -/















/-! ## Transport from recursive to geometric coordinate order -/





/-- `Fin.cast` commutes with the canonical `succAbove` embedding. -/
theorem cast_succAbove
    {n m : ℕ} (h : n = m)
    (p : Fin (n + 1)) (i : Fin n) :
    Fin.cast (congrArg (fun q => q + 1) h)
        (p.succAbove i) =
      (Fin.cast (congrArg (fun q => q + 1) h) p).succAbove
        (Fin.cast h i) := by
  subst m
  rfl





















/-! ## The same selector in recursive arity order -/









































end Wikipedia.SzemeredisTheorem

end
/-!
# Pointwise stage identities for relative counting

This file turns the stage equivalence from
`RelativeCountingDecoder` into closed formulas for the majorants generated
by repeated `MajorizedCutSystem.next`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Prefixing the processed endpoint choices -/
/-! ## Closed formula for an iterated designated majorant -/
/-! ## The selected stage vertices -/
/-! ## Transport from recursive to geometric coordinate order -/

open Wikipedia.SzemeredisTheorem in
@[simp]
theorem solution
    (r s N : ℕ)
    (j : Fin (((s + 1) + r) + 1))
    (x : CubePoint (((s + 1) + r) + 1) N)
    (i : Fin r) :
    (apCSOrderedStageCubeEquiv r s N j x).1.1.pair i =
      (x (j.succAbove
          (csOrderedStageProcessedIndex r s i)) false,
        x (j.succAbove
          (csOrderedStageProcessedIndex r s i)) true) := by
  change
    (apCSStageCubeEquiv r s N
        (apCSStageTransportJ r s j)
        (apCSStageCubeTransportEquiv r s N x)).1.1.pair i =
      _
  rw [apCSStageCubeEquiv_processedPair]
  apply Prod.ext
  · apply congrArg
      (fun q =>
        x q false)
    apply Fin.ext
    have hindex :
        Fin.cast (apCSStageDeletedArityEq r s)
            (csOrderedStageProcessedIndex r s i) =
          Fin.castAdd (s + 1) i := by
      apply Fin.ext
      rfl
    have hsucc :=
      cast_succAbove
        (apCSStageDeletedArityEq r s) j
        (csOrderedStageProcessedIndex r s i)
    rw [hindex] at hsucc
    have hv := congrArg Fin.val hsucc
    simpa [apCSStageTransportJ] using hv.symm
  · apply congrArg
      (fun q =>
        x q true)
    apply Fin.ext
    have hindex :
        Fin.cast (apCSStageDeletedArityEq r s)
            (csOrderedStageProcessedIndex r s i) =
          Fin.castAdd (s + 1) i := by
      apply Fin.ext
      rfl
    have hsucc :=
      cast_succAbove
        (apCSStageDeletedArityEq r s) j
        (csOrderedStageProcessedIndex r s i)
    rw [hindex] at hsucc
    have hv := congrArg Fin.val hsucc
    simpa [apCSStageTransportJ] using hv.symm
