-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:53:30.008861+00:00
-- url     : https://prove2.me/submissions/3f6d838c-1592-4873-b776-485f7223afed

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_polynomialDenseModelError_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_relativeCountingErrorSchedule_diagonal_lt
import Theorems.Thm_Wikipedia_SzemeredisTheorem_relativeCountingErrorSchedule_mono

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Arithmetic-progression face forms as transported cut forms

For a fixed deleted vertex, the arithmetic-progression face form has
coefficients `i - j`.  Coprimality of the modulus with `(k-1)!` makes every
one of these coefficients a unit, so the face form is an automorphic
coordinate sum.  This file proves the coefficient and reindexing facts needed
to apply transported cut discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators









@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl















end Wikipedia.SzemeredisTheorem

end

section





/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

































/-- A deleted `n`-dimensional Boolean cube has `2 ^ n` vertices. -/
theorem card_deletedCube
    {n : ℕ} (j : Fin (n + 1)) :
    Fintype.card (DeletedCube (n + 1) j) = 2 ^ n := by
  calc
    Fintype.card (DeletedCube (n + 1) j) =
        Fintype.card (Fin n → Bool) :=
      Fintype.card_congr (deletedCubeEquiv j).symm
    _ = 2 ^ n := by
      simp [Fintype.card_bool]







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
/-! ## Polynomial dense-model parameters below one scalar budget -/
/-! ## A complete finite transference package -/

open Wikipedia.SzemeredisTheorem.RelativeCountingTransferenceParameters in
/-- Positive density and count reserves yield a complete numerical
transference package. -/
theorem solution
    (r : ℕ) {densityReserve countReserve : ℝ}
    (hdensity : 0 < densityReserve)
    (hcount : 0 < countReserve) :
    Nonempty
      (RelativeCountingTransferenceParameters
        r densityReserve countReserve) := by
  obtain ⟨target, htarget, htargetDensity, htargetOne,
      htargetSchedule⟩ :=
    exists_relativeCountingErrorSchedule_diagonal_lt
      r (r + 2) hdensity hcount
  obtain ⟨p, cutError, approximationError,
      hcutError, happroximationError, hp,
      hmodel_nonneg, hmodel_le⟩ :=
    exists_polynomialDenseModelError_le htarget
  let exponent : ℕ := 2 ^ (r + 1)
  let denseCoefficient : ℝ := (2 : ℝ) ^ exponent
  let crossCoefficient : ℝ :=
    (2 : ℝ) ^ (exponent - 1) *
      (2 : ℝ) ^ exponent
  have hdenseCoefficient : 0 < denseCoefficient := by
    dsimp [denseCoefficient]
    positivity
  have hcrossCoefficient : 0 < crossCoefficient := by
    dsimp [crossCoefficient]
    positivity
  let denseQuotient : ℝ :=
    cutError ^ exponent / (denseCoefficient + 1)
  let crossQuotient : ℝ :=
    target ^ exponent / (crossCoefficient + 1)
  have hdenseQuotient : 0 < denseQuotient := by
    dsimp [denseQuotient]
    positivity
  have hcrossQuotient : 0 < crossQuotient := by
    dsimp [crossQuotient]
    positivity
  let base : ℝ :=
    min 1
      (min target
        (min denseQuotient crossQuotient))
  have hbase : 0 < base := by
    dsimp [base]
    exact
      lt_min zero_lt_one
        (lt_min htarget
          (lt_min hdenseQuotient hcrossQuotient))
  let linearFormsError : ℝ := base / 2
  let crossError : ℝ := target
  have hlinearFormsError : 0 < linearFormsError := by
    dsimp [linearFormsError]
    linarith
  have hcrossError : 0 < crossError := by
    exact htarget
  have hlinearFormsError_le_base :
      linearFormsError ≤ base := by
    dsimp [linearFormsError]
    linarith
  have hbase_one : base ≤ 1 := by
    exact min_le_left _ _
  have hbase_target : base ≤ target := by
    exact
      (min_le_right 1
        (min target
          (min denseQuotient crossQuotient))).trans
        (min_le_left target
          (min denseQuotient crossQuotient))
  have hbase_dense : base ≤ denseQuotient := by
    exact
      (min_le_right 1
        (min target
          (min denseQuotient crossQuotient))).trans
        ((min_le_right target
          (min denseQuotient crossQuotient)).trans
          (min_le_left denseQuotient crossQuotient))
  have hbase_cross : base ≤ crossQuotient := by
    exact
      (min_le_right 1
        (min target
          (min denseQuotient crossQuotient))).trans
        ((min_le_right target
          (min denseQuotient crossQuotient)).trans
          (min_le_right denseQuotient crossQuotient))
  have hlinearFormsError_one :
      linearFormsError ≤ 1 :=
    hlinearFormsError_le_base.trans hbase_one
  have hlinearFormsError_target :
      linearFormsError ≤ target :=
    hlinearFormsError_le_base.trans hbase_target
  have hlinearFormsError_dense :
      linearFormsError ≤ denseQuotient :=
    hlinearFormsError_le_base.trans hbase_dense
  have hlinearFormsError_cross :
      linearFormsError ≤ crossQuotient :=
    hlinearFormsError_le_base.trans hbase_cross
  have hdenseConversion :
      denseCoefficient * linearFormsError ≤
        cutError ^ exponent := by
    have hden :
        0 < denseCoefficient + 1 := by
      linarith
    have hmul :
        linearFormsError * (denseCoefficient + 1) ≤
          cutError ^ exponent :=
      (le_div_iff₀ hden).mp
        (by
          simpa [denseQuotient] using
            hlinearFormsError_dense)
    calc
      denseCoefficient * linearFormsError ≤
          (denseCoefficient + 1) * linearFormsError := by
        exact mul_le_mul_of_nonneg_right
          (by linarith) hlinearFormsError.le
      _ = linearFormsError *
          (denseCoefficient + 1) := by ring
      _ ≤ cutError ^ exponent := hmul
  have hcrossConversionBase :
      crossCoefficient * linearFormsError ≤
        target ^ exponent := by
    have hden :
        0 < crossCoefficient + 1 := by
      linarith
    have hmul :
        linearFormsError * (crossCoefficient + 1) ≤
          target ^ exponent :=
      (le_div_iff₀ hden).mp
        (by
          simpa [crossQuotient] using
            hlinearFormsError_cross)
    calc
      crossCoefficient * linearFormsError ≤
          (crossCoefficient + 1) *
            linearFormsError := by
        exact mul_le_mul_of_nonneg_right
          (by linarith) hlinearFormsError.le
      _ = linearFormsError *
          (crossCoefficient + 1) := by ring
      _ ≤ target ^ exponent := hmul
  have hcrossConversion :
      ∀ j : Fin (r + 2),
        (1 + linearFormsError) ^
              (2 ^ (r + 1) - 1) *
            ((2 : ℝ) ^
                Fintype.card
                  (DeletedCube (r + 2) j) *
              linearFormsError) ≤
          crossError ^ (2 ^ (r + 1)) := by
    intro j
    have hbasePow :
        (1 + linearFormsError) ^ (exponent - 1) ≤
          (2 : ℝ) ^ (exponent - 1) := by
      gcongr
      linarith
    rw [card_deletedCube]
    change
      (1 + linearFormsError) ^ (exponent - 1) *
            ((2 : ℝ) ^ exponent *
              linearFormsError) ≤
        crossError ^ exponent
    calc
      (1 + linearFormsError) ^ (exponent - 1) *
            ((2 : ℝ) ^ exponent *
              linearFormsError) ≤
          (2 : ℝ) ^ (exponent - 1) *
            ((2 : ℝ) ^ exponent *
              linearFormsError) := by
        exact mul_le_mul_of_nonneg_right hbasePow
          (mul_nonneg (by positivity)
            hlinearFormsError.le)
      _ = crossCoefficient * linearFormsError := by
        dsimp [crossCoefficient]
        ring
      _ ≤ target ^ exponent :=
        hcrossConversionBase
      _ = crossError ^ exponent := rfl
  have hschedule :
      relativeCountingErrorSchedule r
          (polynomialDenseModelError
            p cutError approximationError)
          linearFormsError crossError (r + 2) <
        countReserve := by
    have hmono :=
      relativeCountingErrorSchedule_mono r
        hmodel_nonneg hlinearFormsError.le
        hcrossError.le htarget.le
        hmodel_le hlinearFormsError_target
        (le_rfl : crossError ≤ target) (r + 2)
    exact hmono.trans_lt htargetSchedule
  refine ⟨{
    polynomial := p
    cutError := cutError
    approximationError := approximationError
    linearFormsError := linearFormsError
    crossError := crossError
    cutError_pos := hcutError
    approximationError_pos := happroximationError
    linearFormsError_pos := hlinearFormsError
    crossError_pos := hcrossError
    approximates := hp
    denseModelError_nonneg := hmodel_nonneg
    denseModelError_lt := hmodel_le.trans_lt htargetDensity
    denseModel_conversion := ?_
    cross_conversion := hcrossConversion
    comparisonError_lt := hschedule }⟩
  simpa [denseCoefficient, exponent] using
    hdenseConversion
