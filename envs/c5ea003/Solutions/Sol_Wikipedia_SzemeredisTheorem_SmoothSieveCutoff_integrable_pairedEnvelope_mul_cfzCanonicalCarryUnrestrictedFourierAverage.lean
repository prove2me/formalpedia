-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:54:46.690086+00:00
-- url     : https://prove2.me/submissions/6e8b9109-547d-4ab9-a277-81b4776bcfbf

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_integrable_cfzCanonicalCarryTruncationDiscrepancy
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_transformedPairedDivisorFamily_mul_canonicalEulerAverage_eq_unrestricted_add_discrepancy

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





















/-- The cutoff transform is integrable, as needed for pointwise Fourier
inversion. -/
theorem cutoffFourierTransform_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffFourierTransform := by
  change Integrable (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.integrable









@[simp]
theorem norm_inverseFourierCharacter (x t : ℝ) :
    ‖inverseFourierCharacter x t‖ = 1 := by
  rw [inverseFourierCharacter, Complex.norm_exp]
  simp

theorem continuous_inverseFourierCharacter (x : ℝ) :
    Continuous (inverseFourierCharacter x) := by
  unfold inverseFourierCharacter
  fun_prop

/-- Multiplying the integrable Fourier transform by an inverse Fourier
character preserves integrability. -/
theorem integrable_cutoffFourierTransform_mul_inverseFourierCharacter
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t * inverseFourierCharacter x t) := by
  refine χ.cutoffFourierTransform_integrable.mul_bdd
    (c := 1) ?_ ?_
  · exact (continuous_inverseFourierCharacter x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      rw [norm_inverseFourierCharacter]





/-- The cutoff phase is the inverse Fourier character times the real
exponential `exp(-x)`. -/
theorem cutoffMultiplicativePhase_eq
    (x t : ℝ) :
    cutoffMultiplicativePhase x t =
      (Real.exp (-x) : ℂ) * inverseFourierCharacter x t := by
  simp only [cutoffMultiplicativePhase, inverseFourierCharacter,
    Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]



/-- The integrand in the cutoff inversion formula is integrable. -/
theorem integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_inverseFourierCharacter x).mul_const
      (Real.exp (-x) : ℂ)
  convert h using 1
  funext t
  rw [cutoffMultiplicativePhase_eq]
  ring









/-- The integral occurring in a transformed divisor summand is integrable. -/
theorem integrable_transformedSmoothDivisorSummand
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    Integrable
      (fun t : ℝ ↦
        (ArithmeticFunction.moebius d : ℂ) *
          χ.cutoffFourierTransform t *
            divisorMultiplicativePhase R d t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
      (Real.log d / Real.log R)).const_mul
      (ArithmeticFunction.moebius d : ℂ)
  simpa only [divisorMultiplicativePhase, mul_assoc] using h





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
# Multivariate Fourier rewrite of the divisor expansion

The finite Selberg-square expansion has two smooth divisor coefficients for
each form.  Fourier inversion turns those `2 * card κ` coefficients into a
single integral over two copies of `κ → ℝ`.

This file proves that rewrite exactly.  All sum/integral interchanges are
finite, while absolute integrability follows coordinatewise from the
Schwartz transform.  The arithmetic divisibility density is left as an
arbitrary real coefficient, ready for the Euler-product comparison.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff



/-- The coordinatewise transformed divisor family is absolutely
integrable. -/
theorem integrable_transformedDivisorFamilySide
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) :
    Integrable (χ.transformedDivisorFamilySide R d :
      (κ → ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun q =>
    χ.integrable_transformedSmoothDivisorSummand R (d q)





/-- Absolute integrability of one full paired-family integrand. -/
theorem integrable_transformedPairedDivisorFamily
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    Integrable
      (χ.transformedPairedDivisorFamily R z)
      (volume.prod volume) :=
  (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).1)).mul_prod
    (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).2))







/-- Absolute integrability of the full finite divisor-family Fourier
integrand. -/
theorem integrable_divisorExpansionFourierIntegrand
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density : (κ → ℕ × ℕ) → ℝ) :
    Integrable
      (χ.divisorExpansionFourierIntegrand R density)
      (volume.prod volume) := by
  unfold divisorExpansionFourierIntegrand
  apply integrable_finsetSum
  intro z _hz
  exact
    (χ.integrable_transformedPairedDivisorFamily R z).const_mul
      (density z : ℂ)





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
# Summed canonical cyclic-to-Euler boundary

The canonical carry partition compares the cyclic paired-divisibility
density with a divisor-independent affine Euler model.  Its pointwise error
is proportional to the paired-divisor LCM divided by the cyclic modulus.
This file sums that estimate over every divisor family selected by a
Boolean CFZ exponent, restores the Selberg normalization, and records a
joint power-scale limit.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped ArithmeticFunction.Moebius BigOperators













/-! ## Selberg-scaled canonical main terms -/







/-- Pointwise identification of the canonical selected Fourier integrand
with the unrestricted fixed-carry model plus its coordinatewise truncation
discrepancy. -/
theorem
    SmoothSieveCutoff.selectedCFZCanonicalEulerFourierIntegrand_eq_unrestricted_add_discrepancy
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k)
    (t u : SelectedCFZFormIndex e → ℝ) :
    χ.divisorExpansionFourierIntegrand R
        (fun z =>
          cfzCanonicalCarryEulerAverage
            (N := N) W b
            (fun q : SelectedCFZFormIndex e => q.1) z)
        (t, u) =
      pairedCutoffFourierEnvelope χ t u *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R
            (fun q : SelectedCFZFormIndex e => q.1) t u +
        cfzCanonicalCarryTruncationDiscrepancy
          (N := N) χ W b R
          (fun q : SelectedCFZFormIndex e => q.1) t u := by
  simpa only [
    SmoothSieveCutoff.divisorExpansionFourierIntegrand,
    mul_comm] using
    sum_transformedPairedDivisorFamily_mul_canonicalEulerAverage_eq_unrestricted_add_discrepancy
      (N := N) χ W b R
      (fun q : SelectedCFZFormIndex e => q.1) t u







/-! ## A single polynomial joint scale -/























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
/-! ## Exact finite-to-complete main term -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- The finite unrestricted canonical Euler integrand is integrable.  This
is deduced from the original finite divisor Fourier integrand and the exact
coordinatewise truncation splice. -/
theorem
    solution
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b : ℕ) {R : ℕ} (hR : 2 ≤ R)
    (e : LinearFormsExponent k) :
    Integrable
      (fun tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2)
      (volume.prod volume) := by
  let finiteIntegrand :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      χ.divisorExpansionFourierIntegrand R
        (fun z =>
          cfzCanonicalCarryEulerAverage
            (N := N) W b
            (fun q : SelectedCFZFormIndex e => q.1) z)
        tu
  let truncation :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      cfzCanonicalCarryTruncationDiscrepancy
        (N := N) χ W b R
        (fun q : SelectedCFZFormIndex e => q.1)
        tu.1 tu.2
  have hfinite :
      Integrable finiteIntegrand (volume.prod volume) :=
    χ.integrable_divisorExpansionFourierIntegrand R
      (fun z =>
        cfzCanonicalCarryEulerAverage
          (N := N) W b
          (fun q : SelectedCFZFormIndex e => q.1) z)
  have htruncation :
      Integrable truncation (volume.prod volume) := by
    exact
      integrable_cfzCanonicalCarryTruncationDiscrepancy
        χ W b hR
          (fun q : SelectedCFZFormIndex e => q.1)
  have hdifference :
      (fun tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ) =>
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          cfzCanonicalCarryUnrestrictedFourierAverage
            (N := N) W b R
            (fun q : SelectedCFZFormIndex e => q.1)
            tu.1 tu.2) =
        fun tu => finiteIntegrand tu - truncation tu := by
    funext tu
    have hsplice :=
      χ.selectedCFZCanonicalEulerFourierIntegrand_eq_unrestricted_add_discrepancy
        (N := N) R W b e tu.1 tu.2
    dsimp [finiteIntegrand, truncation]
    rw [hsplice]
    ring
  rw [hdifference]
  exact hfinite.sub htruncation
