-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.pow_mul_selectedCFZPairedFourierAbsoluteDensity_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:42:20.240202+00:00
-- url     : https://prove2.me/submissions/9b850c67-146e-4fe4-90d8-f991b5d55a6c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Fourier tails for the smooth sieve cutoff

The Fourier transform used by the smooth Goldston--Yıldırım weight is a
Schwartz function.  This file packages the consequence needed by the
multivariate truncation argument: every polynomially weighted absolute
Fourier moment is integrable, and its mass outside the symmetric interval
`[-T, T]` tends to zero.

The last statements specialize the radius to the conventional growing box
`T = sqrt (log R)`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped Topology

namespace SmoothSieveCutoff



theorem fourierMomentDensity_nonneg
    (χ : SmoothSieveCutoff) (k : ℕ) (t : ℝ) :
    0 ≤ χ.fourierMomentDensity k t := by
  unfold fourierMomentDensity
  positivity















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Finite-product Fourier tails

This file lifts the one-dimensional Schwartz tail estimates for a smooth
sieve cutoff to an arbitrary finite family of Fourier variables.  The
ambient product uses Mathlib's canonical volume measure on `κ → ℝ`, which
is definitionally identified with the finite product of one-dimensional
Lebesgue measures.

The main output is that every coordinatewise polynomially weighted product
of absolute Fourier transforms is integrable and has vanishing mass outside
the sup-norm box of radius `T`, including the standard radius
`sqrt (log R)`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace SmoothSieveCutoff





theorem fourierProductMomentDensity_nonneg
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ)
    (t : κ → ℝ) :
    0 ≤ χ.fourierProductMomentDensity k t := by
  unfold fourierProductMomentDensity
  exact Finset.prod_nonneg fun i _ =>
    χ.fourierMomentDensity_nonneg (k i) (t i)









theorem mem_fourierProductBox_iff
    {κ : Type*} [Fintype κ]
    {T : ℝ} (hT : 0 ≤ T) (t : κ → ℝ) :
    t ∈ fourierProductBox T ↔
      ∀ i, |t i| ≤ T := by
  simp only [fourierProductBox, Metric.mem_closedBall,
    dist_zero_right, pi_norm_le_iff_of_nonneg hT,
    Real.norm_eq_abs]











end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Polylogarithmic closure of the carry Fourier tail

The harmonic LCM mass is bounded by a finite prime product.  The latter is
polylogarithmic, while the cutoff Fourier transform is Schwartz.  This file
makes the quantitative comparison explicit.

For every natural `q`, a finite constant controls

`T ^ q * selectedCFZPairedFourierAbsoluteTail e T`.

Choosing `q` larger than twice the exponent of the prime-product bound makes
the complementary carry Fourier integral vanish at
`T = sqrt (log R)`, without an eventual bounded-mass hypothesis.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace SmoothSieveCutoff

/-! ## Arbitrarily high paired Fourier moments -/



theorem fourierProductMomentDensity_singleCoordinate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (i : κ) (q : ℕ)
    (t : κ → ℝ) :
    χ.fourierProductMomentDensity
        (singleCoordinateMomentExponent i q) t =
      ‖t i‖ ^ q *
        χ.fourierProductMomentDensity (fun _ => 0) t := by
  classical
  unfold fourierProductMomentDensity fourierMomentDensity
    singleCoordinateMomentExponent
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem
    (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem
    (Finset.mem_univ i)]
  simp only [if_pos, pow_zero, one_mul]
  have hprod :
      (∏ j ∈ Finset.univ \ {i},
        (‖t j‖ ^ if j = i then q else 0) *
          ‖χ.cutoffFourierTransform (t j)‖) =
        ∏ j ∈ Finset.univ \ {i},
          ‖χ.cutoffFourierTransform (t j)‖ := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := by
      exact Finset.notMem_singleton.mp
        (Finset.mem_sdiff.mp hj).2
    simp [hji]
  rw [hprod]
  ring



theorem selectedCFZOneSideFourierMomentDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (t : SelectedCFZFormIndex e → ℝ) :
    0 ≤ χ.selectedCFZOneSideFourierMomentDensity e q t := by
  unfold selectedCFZOneSideFourierMomentDensity
  exact Finset.sum_nonneg fun i _ =>
    χ.fourierProductMomentDensity_nonneg
      (singleCoordinateMomentExponent i q) t













theorem pow_mul_fourierProductZeroDensity_le_oneSideMoment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 ≤ T)
    (t : SelectedCFZFormIndex e → ℝ)
    (ht : t ∉ fourierProductBox T) :
    T ^ q * χ.fourierProductMomentDensity (fun _ => 0) t ≤
      χ.selectedCFZOneSideFourierMomentDensity e q t := by
  classical
  have hnotAll :
      ¬∀ i : SelectedCFZFormIndex e, |t i| ≤ T := by
    intro hall
    exact ht ((mem_fourierProductBox_iff hT t).2 hall)
  obtain ⟨i, hi⟩ := Classical.not_forall.mp hnotAll
  have hTi : T ≤ ‖t i‖ := by
    simpa only [Real.norm_eq_abs] using le_of_not_ge hi
  calc
    T ^ q * χ.fourierProductMomentDensity (fun _ => 0) t ≤
        ‖t i‖ ^ q *
          χ.fourierProductMomentDensity (fun _ => 0) t := by
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hT hTi q)
        (χ.fourierProductMomentDensity_nonneg (fun _ => 0) t)
    _ = χ.fourierProductMomentDensity
          (singleCoordinateMomentExponent i q) t := by
      symm
      exact χ.fourierProductMomentDensity_singleCoordinate i q t
    _ ≤ χ.selectedCFZOneSideFourierMomentDensity e q t := by
      unfold selectedCFZOneSideFourierMomentDensity
      exact Finset.single_le_sum
        (fun j _ =>
          χ.fourierProductMomentDensity_nonneg
            (singleCoordinateMomentExponent j q) t)
        (Finset.mem_univ i)









/-! ## Polylogarithmic arithmetic growth -/











/-! ## Cancellation of arithmetic growth by a higher Fourier moment -/









end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# Polylogarithmic closure of the carry Fourier tail

The harmonic LCM mass is bounded by a finite prime product.  The latter is
polylogarithmic, while the cutoff Fourier transform is Schwartz.  This file
makes the quantitative comparison explicit.

For every natural `q`, a finite constant controls

`T ^ q * selectedCFZPairedFourierAbsoluteTail e T`.

Choosing `q` larger than twice the exponent of the prime-product bound makes
the complementary carry Fourier integral vanish at
`T = sqrt (log R)`, without an eventual bounded-mass hypothesis.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Set
open scoped BigOperators Topology
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff
/-! ## Arbitrarily high paired Fourier moments -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
theorem solution
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 ≤ T)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ))
    (htu : tu ∈ (selectedCFZPairedFourierBox e T)ᶜ) :
    T ^ q * χ.selectedCFZPairedFourierAbsoluteDensity e tu ≤
      χ.selectedCFZPairedFourierMomentDensity e q tu := by
  have hnot :
      tu.1 ∉ fourierProductBox T ∨
        tu.2 ∉ fourierProductBox T := by
    by_contra hboth
    apply htu
    push Not at hboth
    unfold selectedCFZPairedFourierBox
    exact ⟨hboth.1, hboth.2⟩
  unfold selectedCFZPairedFourierAbsoluteDensity
    selectedCFZPairedFourierMomentDensity
  rcases hnot with hleft | hright
  · calc
      T ^ q *
          (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2) =
          (T ^ q *
              χ.fourierProductMomentDensity (fun _ => 0) tu.1) *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2 := by
        ring
      _ ≤ χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2 := by
        exact mul_le_mul_of_nonneg_right
          (χ.pow_mul_fourierProductZeroDensity_le_oneSideMoment
            e q hT tu.1 hleft)
          (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2)
      _ ≤
          χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2 +
            χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
              χ.selectedCFZOneSideFourierMomentDensity e q tu.2 := by
        exact le_add_of_nonneg_right
          (mul_nonneg
            (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
            (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.2))
  · calc
      T ^ q *
          (χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            χ.fourierProductMomentDensity (fun _ => 0) tu.2) =
          χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            (T ^ q *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2) := by
        ring
      _ ≤ χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
            χ.selectedCFZOneSideFourierMomentDensity e q tu.2 := by
        exact mul_le_mul_of_nonneg_left
          (χ.pow_mul_fourierProductZeroDensity_le_oneSideMoment
            e q hT tu.2 hright)
          (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
      _ ≤
          χ.selectedCFZOneSideFourierMomentDensity e q tu.1 *
              χ.fourierProductMomentDensity (fun _ => 0) tu.2 +
            χ.fourierProductMomentDensity (fun _ => 0) tu.1 *
              χ.selectedCFZOneSideFourierMomentDensity e q tu.2 := by
        exact le_add_of_nonneg_left
          (mul_nonneg
            (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.1)
            (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2))
