-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.relativeCountingErrorSchedule_mono
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.288832+00:00
-- url     : https://prove2.me/submissions/1846ff2e-1466-433d-8d7d-ed3a6f1d05cd

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingErrorSchedule
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingHeterogeneousMask
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingInduction
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeCountingParameterSelection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSzemeredi
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_ShortInterval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_AdaptiveCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_BoundaryBernoulli
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseAtomBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_CoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_ConditionalAverage
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Energy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FacePartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_FullOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_GrowthFunctionRegularity
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
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleSourceGoodnessBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedAtomEnergy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedBoundaryPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedConfigurationCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedFullBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPatternPartition
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedRemovalTheorem
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedSimplexBridge
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_PreliminaryOrderedRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Regularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Removal
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullBundleRemovalParameters
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullCoarseTargetRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullGoodAtoms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_SourceFullOrderedRemoval
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_StrongOrderedComplexRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_TowerDominatingGrowth
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Unweighted
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_WeakRegularity
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Statement
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
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
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# An explicit error schedule for relative simplex counting

The active-face induction in `RelativeCountingInduction` asks for a scalar
sequence `error`.  Its successor condition is

```text
(1 + ξ) * (3η + 2√(3η) + 2 error(r) + 4ξ)
  ≤ (error(r + 1) - cutError)².
```

This file chooses equality: the next error is `cutError` plus the square
root of the expression on the left.  Nonnegativity of the three input
errors then proves all numerical hypotheses of the active-face induction.
The last section records that every fixed finite stage tends jointly to
zero with the three input errors.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology



@[simp]
theorem relativeCountingErrorSchedule_zero
    (m : ℕ) (cutError η ξ : ℝ) :
    relativeCountingErrorSchedule m cutError η ξ 0 =
      ((m + 2 : ℕ) : ℝ) * cutError :=
  rfl

@[simp]
theorem relativeCountingErrorSchedule_succ
    (m r : ℕ) (cutError η ξ : ℝ) :
    relativeCountingErrorSchedule m cutError η ξ (r + 1) =
      cutError +
        Real.sqrt
          ((1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * relativeCountingErrorSchedule
                m cutError η ξ r + 4 * ξ)) :=
  rfl

/-- Every stage of the schedule is nonnegative when the three input
errors are nonnegative. -/
theorem relativeCountingErrorSchedule_nonneg
    (m : ℕ) {cutError η ξ : ℝ}
    (hcut : 0 ≤ cutError) :
    ∀ r : ℕ, 0 ≤ relativeCountingErrorSchedule m cutError η ξ r := by
  intro r
  induction r with
  | zero =>
      exact mul_nonneg (Nat.cast_nonneg _) hcut
  | succ r _ih =>
      rw [relativeCountingErrorSchedule_succ]
      exact add_nonneg hcut (Real.sqrt_nonneg _)













/-! ## Arithmetic-progression specialization -/





/-! ## Joint smallness at every fixed finite stage -/







end Wikipedia.SzemeredisTheorem

end
/-!
# Small parameters for relative counting

The explicit relative-counting recurrence is continuous at the origin, but
the final transference argument also needs an order-theoretic form of this
fact: replacing any of the three nonnegative input errors by a smaller one
cannot enlarge the scheduled error.

This file first proves that monotonicity and then records a diagonal
small-parameter selector.  These lemmas are the numerical core used when the
polynomial dense-model error and the two linear-forms errors are chosen in a
single parameter package.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open scoped Polynomial

open Wikipedia.SzemeredisTheorem in
/-- The finite relative-counting schedule is monotone in each nonnegative
input error. -/
theorem solution
    (m : ℕ)
    {cutError₁ cutError₂ η₁ η₂ ξ₁ ξ₂ : ℝ}
    (hcut₁ : 0 ≤ cutError₁)
    (hη₁ : 0 ≤ η₁)
    (hξ₁ : 0 ≤ ξ₁) (hξ₂ : 0 ≤ ξ₂)
    (hcut : cutError₁ ≤ cutError₂)
    (hη : η₁ ≤ η₂) (hξ : ξ₁ ≤ ξ₂) :
    ∀ s : ℕ,
      relativeCountingErrorSchedule
          m cutError₁ η₁ ξ₁ s ≤
        relativeCountingErrorSchedule
          m cutError₂ η₂ ξ₂ s := by
  intro s
  induction s with
  | zero =>
      simp only [relativeCountingErrorSchedule_zero]
      exact
        mul_le_mul_of_nonneg_left hcut
          (Nat.cast_nonneg _)
  | succ s ih =>
      rw [relativeCountingErrorSchedule_succ,
        relativeCountingErrorSchedule_succ]
      apply add_le_add hcut
      apply Real.sqrt_le_sqrt
      have hs₁ :
          0 ≤
            relativeCountingErrorSchedule
              m cutError₁ η₁ ξ₁ s :=
        relativeCountingErrorSchedule_nonneg
          m hcut₁ s
      have hs₂ :
          0 ≤
            relativeCountingErrorSchedule
              m cutError₂ η₂ ξ₂ s :=
        relativeCountingErrorSchedule_nonneg
          m (hcut₁.trans hcut) s
      have hsqrt :
          Real.sqrt (3 * η₁) ≤
            Real.sqrt (3 * η₂) := by
        apply Real.sqrt_le_sqrt
        linarith
      have hleft :
          0 ≤ 1 + ξ₁ := by
        linarith
      have hright :
          0 ≤
            3 * η₁ + 2 * Real.sqrt (3 * η₁) +
              2 *
                relativeCountingErrorSchedule
                  m cutError₁ η₁ ξ₁ s +
              4 * ξ₁ := by
        positivity
      have hfirst : 1 + ξ₁ ≤ 1 + ξ₂ := by
        linarith
      have hsecond :
          3 * η₁ + 2 * Real.sqrt (3 * η₁) +
                2 *
                  relativeCountingErrorSchedule
                    m cutError₁ η₁ ξ₁ s +
                4 * ξ₁ ≤
            3 * η₂ + 2 * Real.sqrt (3 * η₂) +
                2 *
                  relativeCountingErrorSchedule
                    m cutError₂ η₂ ξ₂ s +
                4 * ξ₂ := by
        linarith
      exact
        mul_le_mul hfirst hsecond hright
          (by linarith)
