-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasStandardCyclicMajorantLinearForms
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:19:12.405649+00:00
-- url     : https://prove2.me/submissions/8e152086-3fcb-4575-b32d-fa8435516c4f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ArithmeticProgression_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Assembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_CofinalPrimeModulusAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_FinalTransferenceAssembly
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_Chebyshev
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrickDensity
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_ReducedResidueCofinalTransference
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryAverageInterior
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryFourierNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCompleteMainTermBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
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
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_selectedCFZCanonicalCompleteEulerScaledIntegrand_sub_baseline_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_selectedCFZCanonicalEulerFourierMainTerm_sub_one_le_of_interior
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_tendsto_norm_cyclicMajorant_sub_canonicalEulerFourierMainTerm_sieveLevel
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_tendsto_norm_integral_selectedCFZCanonicalArchimedeanBaseline_compl_sqrt_log
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_tendsto_selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_reducedResidues_hasLinearFormsCondition_of_eventually_complex_triangle_error_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_uniform_selectedCFZFiniteFourierCorrection_sieveLevel
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_uniform_cutoff_selectedCFZCanonicalCarryLargePrimeEulerCorrection_close_one

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real













theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)





















/-- The sieve level tends to infinity for every progression length in the
nontrivial range. -/
theorem tendsto_sieveLevel_atTop {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (sieveLevel k) atTop atTop := by
  change Tendsto
    (fun N : ℕ ↦ ⌊(N : ℝ) ^ sieveExponent k⌋₊)
    atTop atTop
  simpa [Function.comp_def] using
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (sieveExponent_pos hk)).comp
        tendsto_natCast_atTop_atTop)







end Wikipedia.SzemeredisTheorem

end

section





namespace Wikipedia.SzemeredisTheorem

open Finset



@[simp]
theorem mem_reducedResidues {W b : ℕ} :
    b ∈ reducedResidues W ↔ b < W ∧ W.Coprime b := by
  simp [reducedResidues]























end Wikipedia.SzemeredisTheorem

end

section



/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm











@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl









end Wikipedia.SzemeredisTheorem

end

section




/-!
# Small-prime local factors for W-tricked affine forms

If `ψ` is an integer affine form, the affine form occurring after the
`W`-trick is

`x ↦ W * ψ(x) + b`.

At a prime `p ∣ W` this form is identically `b` modulo `p`.  When `b` is a
reduced residue modulo `W`, it is therefore nowhere zero modulo `p`.  This
makes every small-prime avoidance factor, including the complex factor
produced by paired Fourier inversion, exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem wTrickedAffineForm_constant {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).constant =
      (W : ℤ) * ψ.constant + b :=
  rfl

@[simp]
theorem wTrickedAffineForm_coefficient {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) (i : ι) :
    (wTrickedAffineForm W b ψ).coefficient i =
      (W : ℤ) * ψ.coefficient i :=
  rfl



























end Wikipedia.SzemeredisTheorem

end
/-!
# The standard cyclic Selberg majorant satisfies the linear-forms condition

This file closes the smooth-sieve input to Green--Tao transference.  Given
a requested error, the primorial cutoff is chosen first so that it covers
the canonical exceptional primes and the uniform arbitrary-carry
large-prime Euler tail.  Only after fixing that cutoff does the cyclic
modulus tend to infinity.

The finite Fourier correction is uniform on the growing box

`T = sqrt (log (sieveLevel k (M + 1)))`.

The complete canonical main term is compared with one through the
baseline-relative interior estimate and the two complementary Fourier
tails.  The cyclic boundary is then added by a final triangle inequality,
followed by finite intersection over the reduced residues and Boolean
selected exponents.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- The standard smooth cyclic Selberg majorant satisfies the exact
linear-forms interface consumed by final Green--Tao transference. -/
theorem solution :
    HasStandardCyclicMajorantLinearForms := by
  classical
  intro k hk η hη
  let χ := standardSmoothSieveCutoff
  let baselineMass : LinearFormsExponent k → ℝ :=
    fun e =>
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
        ∂(volume.prod volume)
  let baselineMassBound : ℝ :=
    1 + ∑ e : LinearFormsExponent k, baselineMass e
  have hmassNonneg :
      ∀ e : LinearFormsExponent k, 0 ≤ baselineMass e := by
    intro e
    dsimp [baselineMass]
    exact integral_nonneg fun _tu => norm_nonneg _
  have hmassBoundPos : 0 < baselineMassBound := by
    have hsum :
        0 ≤ ∑ e : LinearFormsExponent k, baselineMass e :=
      Finset.sum_nonneg fun e _he => hmassNonneg e
    dsimp [baselineMassBound]
    linarith
  have hmassLe :
      ∀ e : LinearFormsExponent k,
        baselineMass e ≤ baselineMassBound := by
    intro e
    have hsingle :
        baselineMass e ≤
          ∑ e' : LinearFormsExponent k, baselineMass e' := by
      exact
        Finset.single_le_sum
          (fun e' _he' => hmassNonneg e')
          (Finset.mem_univ e)
    dsimp [baselineMassBound]
    linarith
  let correctionError : ℝ :=
    η / (18 * baselineMassBound + η)
  have hdenominator :
      0 < 18 * baselineMassBound + η := by
    nlinarith
  have hcorrectionError :
      0 < correctionError := by
    exact div_pos hη hdenominator
  have hcorrectionErrorNonneg :
      0 ≤ correctionError :=
    hcorrectionError.le
  have hcorrectionErrorLeOne :
      correctionError ≤ 1 := by
    dsimp [correctionError]
    exact
      (div_le_one hdenominator).2
        (by nlinarith [hmassBoundPos])
  let interiorError : ℝ :=
    correctionError + correctionError +
      correctionError * correctionError
  have hcorrectionSquare :
      correctionError * correctionError ≤ correctionError := by
    have hproduct :
        0 ≤ correctionError * (1 - correctionError) :=
      mul_nonneg hcorrectionErrorNonneg
        (sub_nonneg.mpr hcorrectionErrorLeOne)
    nlinarith
  have hinteriorErrorNonneg :
      0 ≤ interiorError := by
    dsimp [interiorError]
    positivity
  have hinteriorErrorLe :
      interiorError ≤ 3 * correctionError := by
    dsimp [interiorError]
    nlinarith
  have hthreeCorrectionMass :
      3 * correctionError * baselineMassBound ≤ η / 6 := by
    have hnumerator :
        18 * η * baselineMassBound ≤
          η * (18 * baselineMassBound + η) := by
      nlinarith [sq_nonneg η]
    have hquotient :
        (18 * η * baselineMassBound) /
              (18 * baselineMassBound + η) ≤
            η :=
      (div_le_iff₀ hdenominator).2 hnumerator
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
    calc
      3 * correctionError * baselineMassBound * 6 =
          (18 * η * baselineMassBound) /
            (18 * baselineMassBound + η) := by
        dsimp [correctionError]
        ring
      _ ≤ η := hquotient
  have hinteriorMass :
      ∀ e : LinearFormsExponent k,
        interiorError * baselineMass e ≤ η / 6 := by
    intro e
    calc
      interiorError * baselineMass e ≤
          (3 * correctionError) * baselineMass e :=
        mul_le_mul_of_nonneg_right
          hinteriorErrorLe (hmassNonneg e)
      _ ≤
          3 * correctionError * baselineMassBound :=
        mul_le_mul_of_nonneg_left
          (hmassLe e)
          (mul_nonneg (by norm_num) hcorrectionErrorNonneg)
      _ ≤ η / 6 := hthreeCorrectionMass
  have hkTwo : 2 ≤ k := by omega
  obtain ⟨largePrimeCutoff, hlargePrime⟩ :=
    exists_uniform_cutoff_selectedCFZCanonicalCarryLargePrimeEulerCorrection_close_one
      hkTwo hcorrectionError
  let w : ℕ :=
    max 2
      (max
        (wTrickedCFZComplexExceptionalBound k)
        largePrimeCutoff)
  have hwTwo : 2 ≤ w := by
    exact le_max_left _ _
  have hwCanonical :
      wTrickedCFZComplexExceptionalBound k ≤ w := by
    exact
      (le_max_left
        (wTrickedCFZComplexExceptionalBound k)
        largePrimeCutoff).trans
        (le_max_right 2 _)
  have hwLarge : largePrimeCutoff ≤ w := by
    exact
      (le_max_right
        (wTrickedCFZComplexExceptionalBound k)
        largePrimeCutoff).trans
        (le_max_right 2 _)
  have hwExceptional :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w := by
    exact
      (le_max_left
        (exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q))
        (complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)))).trans
        hwCanonical
  let Nseq : ℕ → ℕ := fun M => M + 1
  let Rseq : ℕ → ℕ :=
    fun M => sieveLevel k (M + 1)
  have hRseq : Tendsto Rseq atTop atTop := by
    exact
      (tendsto_sieveLevel_atTop hk).comp
        (tendsto_add_atTop_nat 1)
  have hRtwo :
      ∀ᶠ M : ℕ in atTop, 2 ≤ Rseq M :=
    hRseq.eventually (eventually_ge_atTop 2)
  have hfiniteN :=
    eventually_uniform_selectedCFZFiniteFourierCorrection_sieveLevel
      hk hwCanonical hcorrectionError
  have hfinite :
      ∀ᶠ M : ℕ in atTop,
        ∀ e : LinearFormsExponent k,
          ∀ tu ∈
              SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq M))),
            ‖selectedCFZCanonicalCommonFiniteCorrection
                  (Rseq M) w tu.1 tu.2 -
                1‖ < correctionError := by
    have hshift :=
      (tendsto_add_atTop_nat 1).eventually hfiniteN
    simpa only [Rseq, Nseq,
      selectedCFZCanonicalCommonFiniteCorrection] using hshift
  refine ⟨w, hwExceptional, ?_⟩
  let ν :
      (M : ℕ) → ℕ → ZMod (M + 1) → ℝ :=
    fun M b =>
      χ.cyclicMajorant
        (sieveLevel k (M + 1))
        (primorial w) b
  let canonicalMainTerm :
      ℕ → ℕ → LinearFormsExponent k → ℂ :=
    fun M b e =>
      letI : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
      χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := M + 1)
        (sieveLevel k (M + 1))
        (primorial w) b e
  have hcyclic :
      ∀ b, b ∈ reducedResidues (primorial w) →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            ‖(mean
                  (linearFormsProduct k (M + 1)
                    (ν M b) e) : ℂ) -
                canonicalMainTerm M b e‖ ≤ η / 2 := by
    intro b hb e
    have hcoprime :
        (primorial w).Coprime b :=
      (mem_reducedResidues.mp hb).2
    have hprimorialTwo : 2 ≤ primorial w := by
      simpa using primorial_mono hwTwo
    have hbPos : 0 < b := by
      apply Nat.pos_of_ne_zero
      intro hbZero
      subst b
      have hprimorialOne : primorial w = 1 := by
        simpa using hcoprime
      omega
    have hboundary :=
      χ.tendsto_norm_cyclicMajorant_sub_canonicalEulerFourierMainTerm_sieveLevel
        (w := w) hk hbPos e
    have hclose :=
      (Metric.tendsto_nhds.mp hboundary)
        (η / 2) (half_pos hη)
    filter_upwards [hclose] with M hM
    have hM' :
        |‖(mean
              (linearFormsProduct k (M + 1)
                (χ.cyclicMajorant
                  (sieveLevel k (M + 1))
                  (primorial w) b) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := M + 1)
              (sieveLevel k (M + 1))
              (primorial w) b e‖| < η / 2 := by
      simpa only [Real.dist_eq, sub_zero] using hM
    simpa only [ν, canonicalMainTerm,
      abs_of_nonneg (norm_nonneg _)] using hM'.le
  have hmainTerm :
      ∀ b, b ∈ reducedResidues (primorial w) →
        ∀ e : LinearFormsExponent k,
          ∀ᶠ M : ℕ in atTop,
            ‖canonicalMainTerm M b e - 1‖ ≤ η / 2 := by
    intro b hb e
    have hcoprime :
        (primorial w).Coprime b :=
      (mem_reducedResidues.mp hb).2
    have hcomplete :=
      χ.tendsto_selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log
        hkTwo
        Nseq (fun _M => w) (fun _M => b) Rseq
        (fun M => Nat.succ_ne_zero M)
        (fun _M => hwExceptional)
        (fun _M => hcoprime)
        hRseq e
    have hcompleteClose :
        ∀ᶠ M : ℕ in atTop,
          χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
              (N := Nseq M) w b (Rseq M) e
              (Real.sqrt (Real.log (Rseq M))) ≤
            η / 6 := by
      have hclose :=
        (Metric.tendsto_nhds.mp hcomplete)
          (η / 6) (by positivity)
      filter_upwards [hclose] with M hM
      have hM' :
          |χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
              (N := Nseq M) w b (Rseq M) e
              (Real.sqrt (Real.log (Rseq M)))| < η / 6 := by
        simpa only [Real.dist_eq, sub_zero] using hM
      exact (le_abs_self _).trans hM'.le
    have hbaseline :=
      χ.tendsto_norm_integral_selectedCFZCanonicalArchimedeanBaseline_compl_sqrt_log
        Rseq hRseq e
    have hbaselineClose :
        ∀ᶠ M : ℕ in atTop,
          ‖∫ tu in
              (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq M))))ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume)‖ ≤
          η / 6 := by
      have hclose :=
        (Metric.tendsto_nhds.mp hbaseline)
          (η / 6) (by positivity)
      filter_upwards [hclose] with M hM
      have hM' :
          |‖∫ tu in
              (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq M))))ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume)‖| < η / 6 := by
        simpa only [Real.dist_eq, sub_zero] using hM
      simpa only [abs_of_nonneg (norm_nonneg _)] using hM'.le
    filter_upwards
        [hRtwo, hfinite, hcompleteClose, hbaselineClose] with
      M hRM hfiniteM hcompleteM hbaselineM
    let : NeZero (Nseq M) := ⟨Nat.succ_ne_zero M⟩
    have hinterior :
        ∀ tu ∈
            SmoothSieveCutoff.selectedCFZPairedFourierBox e
              (Real.sqrt (Real.log (Rseq M))),
          ‖χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
                (N := Nseq M) w b (Rseq M) e tu -
              χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
            interiorError *
              ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ := by
      intro tu htu
      apply
        χ.norm_selectedCFZCanonicalCompleteEulerScaledIntegrand_sub_baseline_le
          hkTwo w b (Rseq M) hwCanonical hcoprime e tu hRM
          hcorrectionErrorNonneg hcorrectionErrorNonneg
      · exact
          (by
            simpa only [
              selectedCFZCanonicalCommonFiniteCorrection] using
              (hfiniteM e tu htu).le)
      · intro carry
        exact
          (hlargePrime
            (selectedCFZCanonicalCarryFourierDataAt
              (N := Nseq M) w b (Rseq M) e carry
              tu.1 tu.2)
            hwLarge hRM).le
    have hmain :=
      χ.norm_selectedCFZCanonicalEulerFourierMainTerm_sub_one_le_of_interior
        (N := Nseq M) hkTwo hwExceptional hcoprime e hRM
        hinteriorErrorNonneg hinterior
    have hmassIdentity :
        (∫ tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ),
          ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
          ∂(volume.prod volume)) =
        baselineMass e := by
      rfl
    rw [hmassIdentity] at hmain
    have hinteriorM := hinteriorMass e
    have hbound :
        ‖χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := Nseq M) (Rseq M)
              (primorial w) b e -
            1‖ ≤ η / 2 := by
      exact hmain.trans (by linarith)
    simpa only [canonicalMainTerm, Nseq, Rseq] using hbound
  have hassembly :=
    eventually_reducedResidues_hasLinearFormsCondition_of_eventually_complex_triangle_error_le
      ν canonicalMainTerm
      (cyclicError := η / 2)
      (mainTermError := η / 2)
      hcyclic hmainTerm
  have hhalf : η / 2 + η / 2 = η := by
    ring
  simpa only [ν, χ, hhalf] using hassembly
