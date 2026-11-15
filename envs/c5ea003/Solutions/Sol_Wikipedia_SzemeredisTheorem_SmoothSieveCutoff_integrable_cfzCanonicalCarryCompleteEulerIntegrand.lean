-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integrable_cfzCanonicalCarryCompleteEulerIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:03:05.934963+00:00
-- url     : https://prove2.me/submissions/b3f824a5-ccb0-4724-ae61-e86161a94aeb

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
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
import Mathlib.Analysis.Normed.Ring.InfiniteProd
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
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_aestronglyMeasurable_cfzCanonicalCarryCompleteEulerIntegrand
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_cfzCanonicalCarryCompleteEulerIntegrand_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier inversion for the smooth sieve cutoff

This file supplies the analytic transform used in the Goldston--Yıldırım
calculation.  For a smooth sieve cutoff `χ`, put

`g(x) = exp(x) χ(x)`.

We regard `g` as complex-valued and use Mathlib's analyst normalization

`𝓕 g(t) = ∫ x, exp(-2 π i x t) g(x)`.

The function `g` is smooth and compactly supported, hence is a Schwartz
function.  Its Fourier transform is therefore again Schwartz and in
particular integrable.  Fourier inversion gives

`χ(x) = ∫ t, 𝓕 g(t) exp(-x + 2 π i t x)`.

At `x = log d / log R`, the last exponential is multiplicative in `d`.
The final results interchange this integral with the finite divisor sums
that occur in the truncated divisor sum.
-/

namespace Wikipedia.SzemeredisTheorem

open Function MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators FourierTransform
  ContDiff SchwartzMap

namespace SmoothSieveCutoff















@[simp]
theorem cutoffFourierSchwartz_apply
    (χ : SmoothSieveCutoff) (t : ℝ) :
    χ.cutoffFourierSchwartz t = χ.cutoffFourierTransform t :=
  rfl













































end SmoothSieveCutoff

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

/-- Every polynomially weighted absolute Fourier moment is integrable. -/
theorem integrable_fourierMomentDensity
    (χ : SmoothSieveCutoff) (k : ℕ) :
    Integrable (χ.fourierMomentDensity k) := by
  change Integrable
    (fun t : ℝ =>
      ‖t‖ ^ k * ‖χ.cutoffFourierTransform t‖)
  simpa only [cutoffFourierSchwartz_apply] using
    χ.cutoffFourierSchwartz.integrable_pow_mul volume k













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



/-- Coordinatewise polynomial moments are integrable on the full finite
product space. -/
theorem integrable_fourierProductMomentDensity
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (k : κ → ℕ) :
    Integrable (χ.fourierProductMomentDensity k :
      (κ → ℝ) → ℝ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun i =>
    χ.integrable_fourierMomentDensity (k i)

















end SmoothSieveCutoff

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

section



/-!
# Honest Fourier-tail bounds for the carry-block divisor expansion

The carry-block Fourier integrand is a finite sum indexed by paired divisor
families.  Taking absolute values before summing loses the cancellation that
will eventually come from the arithmetic Euler product.  This file records
the sharp domination available without making such a cancellation claim.

The loss is isolated in `selectedCFZCarryFourierCoefficientMass`.  Unlike the
raw cardinality `R ^ (2m)`, this quantity retains both the carry-block Euler
coefficient and every Möbius zero.  The remaining analytic factor is a
genuine Schwartz tail, independent of `R`, `W`, `b`, and the divisor family.

Consequently the fully Selberg-scaled complementary integral tends to zero
as soon as the correspondingly scaled coefficient mass is eventually
bounded.  After exceptional-prime coverage, the coefficient mass is further
reduced to a harmonic LCM mass.  The remaining finite combinatorial estimate
is the expected prime-support bound

`harmonicLcmMass R ≤ ∏ p ∈ primesLE R,
  (1 + (2 ^ (2 * m) - 1) / p)`.

Together with the standard zeta-at-`1 + 1 / log R` majorization this is
polylogarithmic, and an arbitrarily high Schwartz moment then beats it at
`T = sqrt (log R)`.  That prime-support estimate is made explicit as the
sole missing step; it is not replaced by the useless raw divisor-choice
count.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace SmoothSieveCutoff

/-! ## The exact coefficient mass retained by triangle domination -/









/-! ## Elementary bounds for the retained arithmetic coefficients -/













/-! ## Harmonic LCM gain when `W` covers the exceptional primes -/























/-! ## The universal paired Schwartz density -/



theorem selectedCFZPairedFourierAbsoluteDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    0 ≤ χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  unfold selectedCFZPairedFourierAbsoluteDensity
  exact mul_nonneg
    (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
    (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2)

theorem integrable_selectedCFZPairedFourierAbsoluteDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    Integrable
      (χ.selectedCFZPairedFourierAbsoluteDensity e)
      (volume.prod volume) := by
  unfold selectedCFZPairedFourierAbsoluteDensity
  exact
    (χ.integrable_fourierProductMomentDensity (fun _ => 0)).mul_prod
      (χ.integrable_fourierProductMomentDensity (fun _ => 0))











/-! ## Pointwise transform domination -/









/-! ## Complementary-integral and scaled bounds -/





/-! ## The exact remaining arithmetic hypothesis -/

























end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section





/-!
# Complete Euler series for the canonical carry model

The canonical divisor expansion naturally produces a finite Euler product
over the primes at most the Selberg radius.  This file defines the honest
complete prime-support series, identifies it with the existing paired
Fourier Euler product, and compares its Fourier integral with the finite
prime-support expression.

There are two logically separate convergence statements.

* At each fixed Fourier frequency the support series is absolutely
  convergent.  In the selected CFZ primorial regime this follows from the
  exact integer coefficient geometry proved below.
* After multiplication by the paired Schwartz envelope, the series is
  absolutely summable in `L¹`.  This is what permits termwise Fourier
  inversion.  It is stronger than pointwise absolute convergence and is
  proved explicitly below rather than inferred from a pointwise `tsum`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## Integer coefficient geometry of canonical carry vectors -/





/-! ## The honest complete support series and Euler integrand -/













/-! ## Expanding one active prime support into nonempty form supports -/











/-! ## A large active prime is killed by full-space Fourier inversion -/





/-! ## A summable uniform majorant and `L¹` convergence -/



theorem selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (p : Nat.Primes) :
    0 ≤ selectedCFZCanonicalCompletePrimeErrorMajorant e R p := by
  unfold selectedCFZCanonicalCompletePrimeErrorMajorant
  positivity







theorem selectedCFZCanonicalCompleteSupportMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (S : Finset Nat.Primes) :
    0 ≤ selectedCFZCanonicalCompleteSupportMajorant e R S := by
  unfold selectedCFZCanonicalCompleteSupportMajorant
  exact Finset.prod_nonneg fun p _hp =>
    selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R p









/-! ## The completion tail as one absolutely convergent series -/





















/-! ## Exact remaining interface for diagonal growing-box decay -/



theorem selectedCFZCanonicalCompleteSupportMass_nonneg
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) :
    0 ≤ selectedCFZCanonicalCompleteSupportMass e R := by
  unfold selectedCFZCanonicalCompleteSupportMass
  exact tsum_nonneg fun S =>
    selectedCFZCanonicalCompleteSupportMajorant_nonneg e R S













end Wikipedia.SzemeredisTheorem

end
/-!
# Canonical complete-Euler main-term bridge

This file joins the two exact full-space cancellations in the canonical
CFZ expansion.

* Coordinatewise divisor truncation has zero full-space Fourier integral.
* Completing the finite prime support to the honest Euler support has zero
  full-space Fourier integral in the primorial exceptional-prime regime.

Consequently the canonical cyclic-boundary main term is exactly the
Selberg-scaled full-space integral of the complete Euler integrand.

The second half separates this integral into the standard growing Fourier
box and its complement.  The completed complement is already uniformly
controlled by `CFZCanonicalEulerCompletionTail`; the sole remaining input
is an interior pointwise comparison with the normalized archimedean
baseline.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators
/-! ## Integrability of the complete canonical Euler model -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Absolute integrability of the complete canonical Euler integrand. -/
theorem solution
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Integrable
      (χ.cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1))
      (volume.prod volume) := by
  let mass := selectedCFZCanonicalCompleteSupportMass e R
  let density :=
    χ.selectedCFZPairedFourierAbsoluteDensity e
  have hmajorant :
      Integrable
        (fun tu :
            (SelectedCFZFormIndex e → ℝ) ×
              (SelectedCFZFormIndex e → ℝ) =>
          mass * density tu)
        (volume.prod volume) :=
    (χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
      mass
  apply hmajorant.mono
  · exact
      χ.aestronglyMeasurable_cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) (w := w) (b := b) e R
  · exact ae_of_all _ fun tu => by
      have hmass :
          0 ≤ mass :=
        selectedCFZCanonicalCompleteSupportMass_nonneg e R
      have hdensity :
          0 ≤ density tu :=
        χ.selectedCFZPairedFourierAbsoluteDensity_nonneg e tu
      simpa only [mass, density, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hmass hdensity)] using
        χ.norm_cfzCanonicalCarryCompleteEulerIntegrand_le
          (N := N) hk hbound hwb e hR tu
