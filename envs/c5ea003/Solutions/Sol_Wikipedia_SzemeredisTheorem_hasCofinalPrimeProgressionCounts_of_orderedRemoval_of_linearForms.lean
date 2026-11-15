-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.hasCofinalPrimeProgressionCounts_of_orderedRemoval_of_linearForms
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:06:36.657583+00:00
-- url     : https://prove2.me/submissions/3d66b859-a825-462d-9c83-f706ba53507b

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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Hom.PowersetCard
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_hasActiveFaceCrossCorrelationLe
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_maskedSimplexComparisonLe_of_activeFaceInduction
import Theorems.Thm_Wikipedia_SzemeredisTheorem_MaskedSimplexComparisonLe_relativeAPComparisonLe_of_allActive
import Theorems.Thm_Wikipedia_SzemeredisTheorem_RelativeCountingTransferenceParameters_nonempty
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount_of_eventually
import Theorems.Thm_Wikipedia_SzemeredisTheorem_eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_relativeCountingErrorSchedule_root

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

theorem primeIntervalConstant_pos :
    0 < primeIntervalConstant := by
  rw [primeIntervalConstant]
  exact div_pos (log_pos (by norm_num)) (by norm_num)

theorem primeScale_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < primeScale k cutoffNormalizer := by
  rw [primeScale]
  exact lt_min (by norm_num)
    (div_pos (sieveExponent_pos hk)
      (mul_pos (by norm_num) hnorm))

theorem primeScale_nonneg {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 ≤ primeScale k cutoffNormalizer :=
  (primeScale_pos hk hnorm).le





theorem densityTarget_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < densityTarget k cutoffNormalizer := by
  rw [densityTarget]
  exact lt_min (by norm_num)
    (div_pos
      (mul_pos (primeScale_pos hk hnorm)
        primeIntervalConstant_pos)
      (by norm_num))











/-- The chosen sieve level is already nonzero at every positive ambient
modulus.  This supplies pointwise nonnegativity of the cyclic majorant even
before any eventual large-modulus threshold is imposed. -/
theorem one_le_sieveLevel
    {k N : ℕ} (hk : 3 ≤ k) (hN : 0 < N) :
    1 ≤ sieveLevel k N := by
  have hNone : 1 ≤ N := hN
  rw [sieveLevel]
  apply Nat.le_floor
  simpa only [Nat.cast_one] using
    Real.one_le_rpow
      (x := (N : ℝ))
      (z := sieveExponent k)
      (by exact_mod_cast hNone)
      (sieveExponent_pos hk).le





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
# Smooth sieve cutoffs

This file packages the smooth cutoff used by the Goldston--Yıldırım
divisor sum.  It also constructs a concrete cutoff from Mathlib's smooth
bump-function infrastructure and proves that its derivative-square
normalizer is positive.
-/

namespace Wikipedia.SzemeredisTheorem

open Function Set MeasureTheory
open scoped ContDiff



namespace SmoothSieveCutoff













theorem normalizer_nonneg (χ : SmoothSieveCutoff) :
    0 ≤ χ.normalizer := by
  rw [normalizer]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro x _
  exact sq_nonneg _







end SmoothSieveCutoff







theorem standardSmoothSieveCutoff_normalizer_pos :
    0 < standardSmoothSieveCutoff.normalizer :=
  standardSmoothSieveCutoff.normalizer_pos



end Wikipedia.SzemeredisTheorem

end

section






/-!
# Smooth truncated divisor sums

The Goldston--Yıldırım majorant is the square of a smoothly truncated
Möbius divisor sum.  This file fixes the normalization and proves the exact
prime-value identity used for pointwise domination of the W-tricked prime
weight.  The later linear-forms estimate is deliberately separated from
these elementary identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators





















theorem smoothSelbergWeight_nonneg
    (χ : ℝ → ℝ) (R n : ℕ) :
    0 ≤ smoothSelbergWeight χ R n :=
  sq_nonneg _











theorem normalizedSelbergMajorant_nonneg
    (χ : ℝ → ℝ) {cχ : ℝ} (hcχ : 0 ≤ cχ)
    {R : ℕ} (hR : 1 ≤ R) (W n : ℕ) :
    0 ≤ normalizedSelbergMajorant χ cχ R W n := by
  unfold normalizedSelbergMajorant
  have hlogR : 0 ≤ Real.log (R : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hR)
  exact div_nonneg
    (mul_nonneg
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (smoothSelbergWeight_nonneg χ R n))
    (mul_nonneg hcχ hlogR)



end Wikipedia.SzemeredisTheorem

end

section




/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl





























































end Wikipedia.SzemeredisTheorem

end

section



/-!
# The smooth cutoff instantiated in the Selberg majorant

This file connects `SmoothSieveCutoff` to the previously total divisor-sum
definitions.  The positivity of the cutoff normalizer discharges every
normalization side condition, including the exact value of the majorant on
primes beyond the sieve level.
-/

namespace Wikipedia.SzemeredisTheorem







theorem SmoothSieveCutoff.majorant_nonneg
    (χ : SmoothSieveCutoff) {R : ℕ} (hR : 1 ≤ R)
    (W n : ℕ) :
    0 ≤ χ.majorant R W n :=
  normalizedSelbergMajorant_nonneg χ.toFun
    χ.normalizer_nonneg hR W n













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
# The global cyclic Selberg majorant

The prime weight is localized to `greenTaoInterval` in order to unwrap a
positive cyclic progression at the end of the proof.  Its transference
majorant does not need the same localization: outside the interval the prime
weight is zero, so any nonnegative majorant is sufficient.

Keeping the smooth Selberg majorant on the whole standard residue system
removes interval indicators from the linear-forms estimate.  This file
defines that global cyclic majorant, proves pointwise domination from the
existing localized theorem, and reindexes every Boolean CFZ subproduct as a
product over its selected subtype.  The latter is the exact interface needed
to apply the generic finite divisor and Fourier expansions to every exponent
tested by `HasLinearFormsCondition`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



theorem SmoothSieveCutoff.cyclicMajorant_nonneg
    {N : ℕ} [NeZero N] (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 ≤ R) (W b : ℕ) (n : ZMod N) :
    0 ≤ χ.cyclicMajorant R W b n :=
  χ.majorant_nonneg hR W (wTrickedValue W b n)

















end Wikipedia.SzemeredisTheorem

end

section


/-!
# Heterogeneous AP-simplex densification states

The one-colour calculation in `RelativeDensification` uses one common
function on every non-distinguished AP face.  This file performs the same
calculation for a family of face weights `g i`.  For a chosen colour `j`,
the product of all other colours is averaged over the missing `j`
coordinate, then truncated at one on the actual deleted-face space
`Fin n → ZMod N`.

The final section packages the full simplex count and the resulting
lower-arity pairing as two different constructors of one payload type.  In
particular, the projected state is not falsely identified with another
`(n + 1)`-colour AP simplex.  It records the bounded surrogate on its real
domain and separately transports all untouched pointwise majorant bounds
along `j.succAbove`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Heterogeneous AP face systems -/





@[simp]
theorem apHeterogeneousSimplexSystem_edge
    (n N : ℕ) (g : APFaceWeightFamily n N)
    (i : Fin (n + 1))
    (x : DeletedVector
      (fun _ : Fin (n + 1) => ZMod N) i) :
    (apHeterogeneousSimplexSystem n N g).edgeWeight i x =
      g i (apSimplexForm (n + 1) N i x) :=
  rfl



















/-! ## Projection bounds -/













/-! ## Exact heterogeneous count and pairing -/













/-! ## A concrete full-to-projected state transition -/































namespace RelativeDensificationIteration



end RelativeDensificationIteration











end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

universe u

/-! ## Factor-independence of structural CFZ certificates -/

namespace MajorizedCutSystem



end MajorizedCutSystem

/-! ## Arbitrary simplex factors under homogeneous AP majorants -/





















/-! ## Active-face cardinality and the comparison invariant -/























/-! ## Replacing one canonical edge by a whole-face function -/



























/-! ## The exact mixed-copy strong-linear-forms interface -/





















/-! ## Direct cut term and projected pointwise bounds -/















/-! ## Truncation and the lower-cardinality quadratic term -/







/-! ## One active-face recurrence -/









/-- Fully decoded active-face induction.

The copy-dependent cross correlations are now internal consequences of the
same linear-forms condition, so callers need only provide the numerical
error schedule. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_of_linearForms
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    {cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (error : ℕ → ℝ)
    (hbase :
      (((m + 2 : ℕ) : ℝ) * cutError) ≤ error 0)
    (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1)))
    (hnext :
      ∀ r : ℕ, cutError ≤ error (r + 1))
    (hroot :
      ∀ r : ℕ,
        (1 + ξ) *
            (3 * η + 2 * Real.sqrt (3 * η) +
              2 * error r + 4 * ξ) ≤
          (error (r + 1) - cutError) ^ 2)
    (active : Fin (m + 2) → Bool) :
    MaskedSimplexComparisonLe (m + 1) N ν active
      cutError (error (activeFaceCount active)) := by
  exact
    hLF.maskedSimplexComparisonLe_of_activeFaceInduction
      hν error hbase
      (fun current j _hj =>
        hLF.hasActiveFaceCrossCorrelationLe
          hν current j hξ (hconvert j))
      hξ hconvert hnext hroot active

end Wikipedia.SzemeredisTheorem

end

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



/-- The schedule has exactly the base budget required by relative
counting. -/
theorem relativeCountingErrorSchedule_base
    (m : ℕ) (cutError η ξ : ℝ) :
    ((m + 2 : ℕ) : ℝ) * cutError ≤
      relativeCountingErrorSchedule m cutError η ξ 0 := by
  rw [relativeCountingErrorSchedule_zero]

/-- Every successor budget contains at least the direct face-cut error. -/
theorem relativeCountingErrorSchedule_next
    (m : ℕ) (cutError η ξ : ℝ) :
    ∀ r : ℕ,
      cutError ≤
        relativeCountingErrorSchedule m cutError η ξ (r + 1) := by
  intro r
  rw [relativeCountingErrorSchedule_succ]
  exact le_add_of_nonneg_right (Real.sqrt_nonneg _)



/-- The explicit schedule discharges every scalar hypothesis of fully
decoded relative counting. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_of_errorSchedule
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1)))
    (active : Fin (m + 2) → Bool) :
    MaskedSimplexComparisonLe (m + 1) N ν active cutError
      (relativeCountingErrorSchedule m cutError η ξ
        (activeFaceCount active)) := by
  exact
    hLF.maskedSimplexComparisonLe_of_linearForms
      hν
      (relativeCountingErrorSchedule m cutError η ξ)
      (relativeCountingErrorSchedule_base m cutError η ξ)
      hξ hconvert
      (relativeCountingErrorSchedule_next m cutError η ξ)
      (relativeCountingErrorSchedule_root m hcut hη hξ)
      active

/-- The all-active mask has one active face for each element of its
finite index type. -/
@[simp]
theorem activeFaceCount_allActive (k : ℕ) :
    activeFaceCount (fun _ : Fin k => true) = k := by
  simp [activeFaceCount, activeFaceSet]

/-- Convenient all-active form of the explicit relative-counting
comparison. -/
theorem HasLinearFormsCondition.maskedSimplexComparisonLe_allActive_of_errorSchedule
    {m N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (m + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (m + 2),
        (1 + η) ^ (2 ^ (m + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (m + 2) j) * η) ≤
          ξ ^ (2 ^ (m + 1))) :
    MaskedSimplexComparisonLe (m + 1) N ν
      (fun _ => true) cutError
      (relativeCountingErrorSchedule m cutError η ξ (m + 2)) := by
  simpa using
    hLF.maskedSimplexComparisonLe_of_errorSchedule
      hν hcut hη hξ hconvert (fun _ => true)

/-! ## Arithmetic-progression specialization -/



/-- The explicit schedule therefore gives quantitative relative counting
for cyclic arithmetic progressions of length `r + 2`. -/
theorem HasLinearFormsCondition.relativeAPComparisonLe_of_errorSchedule
    {r N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η cutError ξ : ℝ}
    (hLF : HasLinearFormsCondition (r + 2) N ν η)
    (hν : ∀ z, 0 ≤ ν z)
    (hcut : 0 ≤ cutError) (hη : 0 ≤ η) (hξ : 0 ≤ ξ)
    (hconvert :
      ∀ j : Fin (r + 2),
        (1 + η) ^ (2 ^ (r + 1) - 1) *
            ((2 : ℝ) ^
              Fintype.card (DeletedCube (r + 2) j) * η) ≤
          ξ ^ (2 ^ (r + 1)))
    (hN : Nat.Coprime N (Nat.factorial (r + 1))) :
    RelativeAPComparisonLe r N ν cutError
      (relativeCountingErrorSchedule r cutError η ξ (r + 2)) := by
  exact
    (hLF.maskedSimplexComparisonLe_allActive_of_errorSchedule
      hν hcut hη hξ hconvert).relativeAPComparisonLe_of_allActive hN

/-! ## Joint smallness at every fixed finite stage -/







end Wikipedia.SzemeredisTheorem

end

section


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

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped Polynomial







/-! ## Polynomial dense-model parameters below one scalar budget -/



/-! ## A complete finite transference package -/





/-! ## Instantiating the comparison callback -/

/-- A relative AP comparison remains valid after enlarging its scalar count
error. -/
theorem RelativeAPComparisonLe.mono_countError
    {r N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {cutError countError₁ countError₂ : ℝ}
    (hcomparison :
      RelativeAPComparisonLe
        r N ν cutError countError₁)
    (hcount : countError₁ ≤ countError₂) :
    RelativeAPComparisonLe
      r N ν cutError countError₂ := by
  intro f g hf0 hfν hg hcut
  exact
    (hcomparison f g hf0 hfν hg hcut).trans hcount

/-- The selected package turns a linear-forms condition at its chosen error
into the comparison callback needed by cofinal prime transference. -/
theorem RelativeCountingTransferenceParameters.relativeAPComparisonLe
    {r N : ℕ} [NeZero N]
    {densityReserve countReserve : ℝ}
    (P : RelativeCountingTransferenceParameters
      r densityReserve countReserve)
    {ν : ZMod N → ℝ}
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν P.linearFormsError)
    (hν : ∀ z, 0 ≤ ν z)
    (hN : Nat.Coprime N (Nat.factorial (r + 1))) :
    RelativeAPComparisonLe r N ν
      (polynomialDenseModelError
        P.polynomial P.cutError P.approximationError)
      countReserve := by
  apply RelativeAPComparisonLe.mono_countError
    (hLF.relativeAPComparisonLe_of_errorSchedule
      hν P.denseModelError_nonneg
      P.linearFormsError_pos.le
      P.crossError_pos.le
      P.cross_conversion hN)
  exact P.comparisonError_lt.le

end Wikipedia.SzemeredisTheorem

end
/-!
# Final dense/relative/sieve transference assembly

All elementary prime-density and extraction steps are already packaged by
`ReducedResidueCofinalTransference`.  This file performs the remaining
quantifier bookkeeping between the three deep inputs:

* ordered hypergraph removal, hence a positive uniform weighted dense AP
  count;
* the explicit relative-counting parameter package;
* the smooth cyclic-majorant linear-forms estimate.

The output is the corrected reduced-residue, cofinal-prime count predicate
consumed by the benchmark-facing theorem.  In particular the W-trick cutoff
is selected after the relative error, while the cyclic modulus is selected
only afterwards.
-/
open Wikipedia.SzemeredisTheorem
open Filter

open Wikipedia.SzemeredisTheorem in
/-- Ordered removal and the standard smooth-sieve linear-forms estimate
supply the corrected cofinal-prime count predicate. -/
theorem
    solution
    (hremoval : HasOrderedRemovalForAllAPLengths)
    (hsieve : HasStandardCyclicMajorantLinearForms) :
    HasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts := by
  intro k hk
  let density := densityTarget k standardSmoothSieveCutoff.normalizer
  have hdensity : 0 < density := by
    exact densityTarget_pos hk standardSmoothSieveCutoff_normalizer_pos
  let denseThreshold := density / 2
  have hdenseThreshold : 0 < denseThreshold := by
    dsimp [denseThreshold]
    linarith
  obtain ⟨denseCount, hdenseCount, hweighted⟩ :=
    exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
      k (by omega) (hremoval k hk) hdenseThreshold
  let countReserve := denseCount / 2
  have hcountReserve : 0 < countReserve := by
    dsimp [countReserve]
    linarith
  let r := k - 2
  obtain ⟨P⟩ :=
    RelativeCountingTransferenceParameters.nonempty
      r hdenseThreshold hcountReserve
  obtain ⟨w, _hwExceptional, hlinearForms⟩ :=
    hsieve k hk P.linearFormsError P.linearFormsError_pos
  let W := primorial w
  let ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ :=
    fun M b =>
      standardSmoothSieveCutoff.cyclicMajorant
        (sieveLevel k (M + 1)) W b
  have hcolors : r + 2 = k := by
    dsimp [r]
    omega
  have hrank : r + 1 = k - 1 := by
    dsimp [r]
    omega
  have hν_nonneg :
      ∀ M b (x : ZMod (M + 1)), 0 ≤ ν M b x := by
    intro M b x
    exact
      standardSmoothSieveCutoff.cyclicMajorant_nonneg
        (one_le_sieveLevel hk (Nat.succ_pos M)) W b x
  have hmajor :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          ∀ x : ZMod (M + 1),
            wTrickedPrimeWeight
                (primeScale k
                  standardSmoothSieveCutoff.normalizer)
                W b x ≤
              ν M b x := by
    have hbase :=
      eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant
        standardSmoothSieveCutoff hk (primorial_pos w)
    filter_upwards [hbase] with M hM
    intro b hb x
    exact hM b (mem_reducedResidues.mp hb).1 x
  have hLF :
      ∀ᶠ M : ℕ in atTop,
        ∀ b, b ∈ reducedResidues W →
          HasLinearFormsCondition
            (r + 2) (M + 1) (ν M b)
              P.linearFormsError := by
    simpa only [W, ν, hcolors] using hlinearForms
  have hcofinalSmall :
      CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
        (r + 2)
        (primeScale k standardSmoothSieveCutoff.normalizer)
        W
        (denseThreshold +
          polynomialDenseModelError
            P.polynomial P.cutError P.approximationError)
        (denseCount - countReserve) := by
    apply
      cofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount_of_eventually
        ν
        (r := r)
        (α := primeScale k standardSmoothSieveCutoff.normalizer)
        (linearFormsError := P.linearFormsError)
        (cutError := P.cutError)
        (approximationError := P.approximationError)
        (p := P.polynomial)
        (δ := denseThreshold)
        (denseCount := denseCount)
        (countError := countReserve)
    · exact
        primeScale_nonneg hk
          standardSmoothSieveCutoff_normalizer_pos
    · exact P.approximationError_pos.le
    · exact P.cutError_pos.le
    · exact P.approximates
    · exact P.denseModel_conversion
    · simpa only [hcolors] using hweighted
    · exact hν_nonneg
    · exact hmajor
    · exact hLF
    · intro M b hcoprime hLFM
      exact
        P.relativeAPComparisonLe hLFM
          (hν_nonneg M b) hcoprime
  have hdensityThreshold :
      denseThreshold +
          polynomialDenseModelError
            P.polynomial P.cutError P.approximationError ≤
        density := by
    have hmodel := P.denseModelError_lt
    dsimp [denseThreshold] at hmodel ⊢
    linarith
  have hcountPositive :
      0 < denseCount - countReserve := by
    dsimp [countReserve]
    linarith
  refine ⟨w, denseCount - countReserve, hcountPositive, ?_⟩
  simpa only [hcolors, W, density] using
    (show
      CofinalPrimeUniformReducedResidueWTrickedPrimeProgressionCount
        (r + 2)
        (primeScale k standardSmoothSieveCutoff.normalizer)
        W density (denseCount - countReserve) from
      by
        intro M₀
        obtain ⟨M, hM, hprime, hMtransfer⟩ :=
          hcofinalSmall M₀
        refine ⟨M, hM, hprime, ?_⟩
        intro b hb hmean
        exact
          hMtransfer b hb
            (hdensityThreshold.trans hmean))
