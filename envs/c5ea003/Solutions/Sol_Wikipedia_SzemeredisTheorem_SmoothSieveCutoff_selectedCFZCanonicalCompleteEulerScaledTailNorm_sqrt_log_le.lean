-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm_sqrt_log_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:07:13.117863+00:00
-- url     : https://prove2.me/submissions/a3f5582e-651b-4bc9-abaa-3872eaec430f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_selectedCFZCanonicalCompleteEulerScaledSupportMass_le_polylog
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_selectedCFZCanonicalCompleteEulerScaledTailNorm_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_selectedCFZPairedFourierAbsoluteTail_sqrt_log_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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





theorem selectedCFZPairedFourierAbsoluteMoment_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (q : ℕ) :
    0 ≤ χ.selectedCFZPairedFourierAbsoluteMoment e q := by
  unfold selectedCFZPairedFourierAbsoluteMoment
  exact integral_nonneg fun tu =>
    χ.selectedCFZPairedFourierMomentDensity_nonneg e q tu











/-! ## Polylogarithmic arithmetic growth -/











/-! ## Cancellation of arithmetic growth by a higher Fourier moment -/









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

section



/-!
# Polylogarithmic control of the canonical Euler-completion tail

The complete-support majorant has local factor

`1 + 3m p^(-1-1/log R) + 4^m p^(-2)`,

where `m` is the number of selected CFZ forms.  We compare its two
nonconstant pieces with the Euler products for
`ζ(1 + 1 / log R)` and `ζ(2)`.  The elementary bound
`‖ζ(1 + 1 / log R)‖ ≤ 1 + log R` then gives an explicit
polylogarithmic bound for the whole infinite support mass, and hence for
the genuinely missing completion tail.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## A two-factor Euler comparison -/





/-! ## The infinite support mass -/















/-! ## Pointwise and complementary-box bounds -/











/-! ## The completed Euler model on the complementary box -/







/-! ## Selberg-scaled complementary contributions -/



theorem
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass_nonneg
    {k : ℕ} (χ : SmoothSieveCutoff)
    (w R : ℕ) (e : LinearFormsExponent k) :
    0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
  exact mul_nonneg
    (mul_nonneg
      (pow_nonneg (abs_nonneg _) _)
      (pow_nonneg (abs_nonneg _) _))
    (selectedCFZCanonicalCompleteSupportMass_nonneg e R)





















/-! ## High moments and schedule-uniform decay -/











end Wikipedia.SzemeredisTheorem

end
/-!
# Polylogarithmic control of the canonical Euler-completion tail

The complete-support majorant has local factor

`1 + 3m p^(-1-1/log R) + 4^m p^(-2)`,

where `m` is the number of selected CFZ forms.  We compare its two
nonconstant pieces with the Euler products for
`ζ(1 + 1 / log R)` and `ζ(2)`.  The elementary bound
`‖ζ(1 + 1 / log R)‖ ≤ 1 + log R` then gives an explicit
polylogarithmic bound for the whole infinite support mass, and hence for
the genuinely missing completion tail.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators
/-! ## A two-factor Euler comparison -/
/-! ## The infinite support mass -/
/-! ## Pointwise and complementary-box bounds -/
/-! ## The completed Euler model on the complementary box -/
/-! ## Selberg-scaled complementary contributions -/
/-! ## High moments and schedule-uniform decay -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Quantitative high-moment bound for the scaled completed Euler model. -/
theorem
    solution
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e (Real.sqrt (Real.log R)) ≤
      (χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
        χ.selectedCFZPairedFourierAbsoluteMoment e
          (2 *
            (selectedCFZCanonicalCompleteEulerScaledPolylogExponent e + 1))) *
        ((1 + Real.log R) ^
            selectedCFZCanonicalCompleteEulerScaledPolylogExponent e /
          (Real.log R) ^
            (selectedCFZCanonicalCompleteEulerScaledPolylogExponent e + 1)) := by
  let E := selectedCFZCanonicalCompleteEulerScaledPolylogExponent e
  let C := χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e
  let M :=
    χ.selectedCFZPairedFourierAbsoluteMoment e (2 * (E + 1))
  have hscaled :
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e ≤
        C * (1 + Real.log R) ^ E := by
    simpa only [C, E] using
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass_le_polylog
        w e hR
  have hscaledNonneg :
      0 ≤ χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e :=
    χ.selectedCFZCanonicalCompleteEulerScaledSupportMass_nonneg w R e
  have hmoment :
      χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) ≤
        M / (Real.log R) ^ (E + 1) := by
    simpa only [M] using
      χ.selectedCFZPairedFourierAbsoluteTail_sqrt_log_le
        e (E + 1) hR
  have hM : 0 ≤ M :=
    χ.selectedCFZPairedFourierAbsoluteMoment_nonneg e (2 * (E + 1))
  have hlog : 0 < Real.log R :=
    Real.log_pos (by exact_mod_cast hR : (1 : ℝ) < R)
  have hquotient :
      0 ≤ M / (Real.log R) ^ (E + 1) :=
    div_nonneg hM (pow_nonneg hlog.le _)
  calc
    χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e (Real.sqrt (Real.log R)) ≤
      χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
        χ.selectedCFZPairedFourierAbsoluteTail e
          (Real.sqrt (Real.log R)) :=
      χ.selectedCFZCanonicalCompleteEulerScaledTailNorm_le
        (N := N) hk hbound hwb e hR _
    _ ≤
        χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e *
          (M / (Real.log R) ^ (E + 1)) :=
      mul_le_mul_of_nonneg_left hmoment hscaledNonneg
    _ ≤
        (C * (1 + Real.log R) ^ E) *
          (M / (Real.log R) ^ (E + 1)) :=
      mul_le_mul_of_nonneg_right hscaled hquotient
    _ =
        (C * M) *
          ((1 + Real.log R) ^ E /
            (Real.log R) ^ (E + 1)) := by
      ring
    _ = _ := by rfl
