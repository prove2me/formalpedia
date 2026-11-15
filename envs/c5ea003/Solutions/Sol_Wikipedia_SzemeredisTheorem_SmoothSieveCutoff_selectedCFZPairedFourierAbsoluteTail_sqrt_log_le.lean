-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:44:18.221287+00:00
-- url     : https://prove2.me/submissions/5f4021ec-3210-49d1-a0db-1a9a8ef7d3e7

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_pow_mul_selectedCFZPairedFourierAbsoluteDensity_le_moment

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
# Fourier inversion with the CFZ carry-block average retained

The carry decomposition does not produce one common arithmetic Euler
product.  For a paired divisor family `z`, both the quotient-block box and
the local prime product depend on `pairedDivisorLcm z`.  This file keeps
that dependence inside the finite divisor sum and applies Fourier inversion
only to the smooth coefficient of each individual family.

Thus the exact integrand below has the honest shape

`∑ z, (mean over the quotient blocks belonging to z) *
  (transformed coefficient belonging to z)`.

No multiplicative closure of the truncated choices `d ≤ R` is used.  The
last results also split the exact integral into a finite Fourier box and its
complement, providing the interface needed for a subsequent uniform
Fourier-box comparison and tail estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## The blockwise arithmetic coefficient -/







/-! ## The carry-dependent Fourier integrand -/









/-! ## Exact divisor-sum and scaled-main-term bridges -/





/-! ## Exact finite-box decomposition -/



theorem measurableSet_selectedCFZPairedFourierBox
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    MeasurableSet (selectedCFZPairedFourierBox e T) := by
  unfold selectedCFZPairedFourierBox fourierProductBox
  exact
    Metric.isClosed_closedBall.measurableSet.prod
      Metric.isClosed_closedBall.measurableSet





end SmoothSieveCutoff

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







theorem selectedCFZOneSideFourierMomentDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (t : SelectedCFZFormIndex e → ℝ) :
    0 ≤ χ.selectedCFZOneSideFourierMomentDensity e q t := by
  unfold selectedCFZOneSideFourierMomentDensity
  exact Finset.sum_nonneg fun i _ =>
    χ.fourierProductMomentDensity_nonneg
      (singleCoordinateMomentExponent i q) t

theorem integrable_selectedCFZOneSideFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) :
    Integrable
      (χ.selectedCFZOneSideFourierMomentDensity e q) := by
  unfold selectedCFZOneSideFourierMomentDensity
  exact integrable_finsetSum Finset.univ fun i _ =>
    χ.integrable_fourierProductMomentDensity
      (singleCoordinateMomentExponent i q)



theorem selectedCFZPairedFourierMomentDensity_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    0 ≤ χ.selectedCFZPairedFourierMomentDensity e q tu := by
  unfold selectedCFZPairedFourierMomentDensity
  exact add_nonneg
    (mul_nonneg
      (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.1)
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.2))
    (mul_nonneg
      (χ.fourierProductMomentDensity_nonneg (fun _ => 0) tu.1)
      (χ.selectedCFZOneSideFourierMomentDensity_nonneg e q tu.2))

theorem integrable_selectedCFZPairedFourierMomentDensity
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) :
    Integrable
      (χ.selectedCFZPairedFourierMomentDensity e q)
      (volume.prod volume) := by
  unfold selectedCFZPairedFourierMomentDensity
  exact
    ((χ.integrable_selectedCFZOneSideFourierMomentDensity e q).mul_prod
      (χ.integrable_fourierProductMomentDensity (fun _ => 0))).add
    ((χ.integrable_fourierProductMomentDensity (fun _ => 0)).mul_prod
      (χ.integrable_selectedCFZOneSideFourierMomentDensity e q))









theorem pow_mul_selectedCFZPairedFourierAbsoluteTail_le_moment
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    T ^ q * χ.selectedCFZPairedFourierAbsoluteTail e T ≤
      χ.selectedCFZPairedFourierAbsoluteMoment e q := by
  unfold selectedCFZPairedFourierAbsoluteTail
    selectedCFZPairedFourierAbsoluteMoment
  calc
    T ^ q *
        (∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZPairedFourierAbsoluteDensity e tu
          ∂(volume.prod volume)) =
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          T ^ q * χ.selectedCFZPairedFourierAbsoluteDensity e tu
          ∂(volume.prod volume) := by
      rw [integral_const_mul]
    _ ≤
        ∫ tu in (selectedCFZPairedFourierBox e T)ᶜ,
          χ.selectedCFZPairedFourierMomentDensity e q tu
          ∂(volume.prod volume) := by
      apply setIntegral_mono_on
      · exact
          ((χ.integrable_selectedCFZPairedFourierAbsoluteDensity e).const_mul
            (T ^ q)).integrableOn
      · exact
          (χ.integrable_selectedCFZPairedFourierMomentDensity e q).integrableOn
      · exact (measurableSet_selectedCFZPairedFourierBox e T).compl
      · intro tu htu
        exact
          χ.pow_mul_selectedCFZPairedFourierAbsoluteDensity_le_moment
            e q hT tu htu
    _ ≤
        ∫ tu,
          χ.selectedCFZPairedFourierMomentDensity e q tu
          ∂(volume.prod volume) := by
      exact setIntegral_le_integral
        (χ.integrable_selectedCFZPairedFourierMomentDensity e q)
        (Filter.Eventually.of_forall fun tu =>
          χ.selectedCFZPairedFourierMomentDensity_nonneg e q tu)

theorem selectedCFZPairedFourierAbsoluteTail_le_moment_div_pow
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ)
    {T : ℝ} (hT : 0 < T) :
    χ.selectedCFZPairedFourierAbsoluteTail e T ≤
      χ.selectedCFZPairedFourierAbsoluteMoment e q / T ^ q := by
  rw [le_div_iff₀ (pow_pos hT q)]
  simpa only [mul_comm] using
    χ.pow_mul_selectedCFZPairedFourierAbsoluteTail_le_moment
      e q hT.le



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
    (e : LinearFormsExponent k) (n : ℕ)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZPairedFourierAbsoluteTail e
        (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZPairedFourierAbsoluteMoment e (2 * n) /
        (Real.log R) ^ n := by
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log R := Real.log_pos hRone
  have hsqrt : 0 < Real.sqrt (Real.log R) :=
    Real.sqrt_pos.2 hlog
  have hpow :
      Real.sqrt (Real.log R) ^ (2 * n) =
        (Real.log R) ^ n := by
    calc
      Real.sqrt (Real.log R) ^ (2 * n) =
          (Real.sqrt (Real.log R) ^ 2) ^ n := by
        rw [pow_mul]
      _ = (Real.log R) ^ n := by
        rw [Real.sq_sqrt hlog.le]
  rw [← hpow]
  exact
    χ.selectedCFZPairedFourierAbsoluteTail_le_moment_div_pow
      e (2 * n) hsqrt
