-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalEulerFourierMainTerm_eq_completeEulerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:04:24.944321+00:00
-- url     : https://prove2.me/submissions/b7d10f31-be1d-452a-b629-38e2ad6451ff

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integrable_cfzCanonicalCarryCompleteEulerIntegrand
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_cfzCanonicalCarryEulerCompletionDiscrepancy_eq_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_integrable_cfzCanonicalCarryTruncationDiscrepancy
import Theorems.Thm_Wikipedia_SzemeredisTheorem_integral_cfzCanonicalCarryTruncationDiscrepancy_eq_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_transformedPairedDivisorFamily_mul_canonicalEulerAverage_eq_unrestricted_add_discrepancy

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

/-- Exact integral form of the canonical unrestricted-plus-truncation
splice. -/
theorem
    SmoothSieveCutoff.selectedCFZEulerFourierMainTerm_eq_integral_unrestricted_add_discrepancy
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff) (R W b : ℕ)
    (e : LinearFormsExponent k) :
    χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := N) R W b e =
      (normalizedSelbergScale χ.normalizer R W : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                cfzCanonicalCarryUnrestrictedFourierAverage
                  (N := N) W b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  tu.1 tu.2 +
              cfzCanonicalCarryTruncationDiscrepancy
                (N := N) χ W b R
                (fun q : SelectedCFZFormIndex e => q.1)
                tu.1 tu.2)
            ∂(volume.prod volume)) := by
  unfold selectedCFZCanonicalEulerFourierMainTerm
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ fun tu =>
    χ.selectedCFZCanonicalEulerFourierIntegrand_eq_unrestricted_add_discrepancy
      (N := N) R W b e tu.1 tu.2





/-! ## A single polynomial joint scale -/























end Wikipedia.SzemeredisTheorem

end

section




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

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## Integrability of the complete canonical Euler model -/





/-! ## Exact finite-to-complete main term -/



/-- The Euler-completion discrepancy is integrable. -/
theorem
    SmoothSieveCutoff.integrable_cfzCanonicalCarryEulerCompletionDiscrepancy
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
      (χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1))
      (volume.prod volume) := by
  unfold SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy
  exact
    (χ.integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
      (N := N) (primorial w) b hR e).sub
      (χ.integrable_cfzCanonicalCarryCompleteEulerIntegrand
        (N := N) hk hbound hwb e hR)



/-! ## Scaled integrand and normalized archimedean baseline -/























/-! ## Interior comparison and the complete integration estimate -/





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
/-- **Exact complete-main-term identity.**  In the primorial regime, the
canonical Fourier main term is exactly the Selberg-scaled full-space
integral of the honest complete Euler integrand. -/
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
    χ.selectedCFZCanonicalEulerFourierMainTerm
        (N := N) R (primorial w) b e =
      (normalizedSelbergScale
          χ.normalizer R (primorial w) : ℂ) ^
          Fintype.card (SelectedCFZFormIndex e) *
        (((Real.log R ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex e) *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            χ.cfzCanonicalCarryCompleteEulerIntegrand
              (N := N) (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1) tu
            ∂(volume.prod volume)) := by
  let unrestricted :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        cfzCanonicalCarryUnrestrictedFourierAverage
          (N := N) (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          tu.1 tu.2
  let truncation :=
    fun tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ) =>
      cfzCanonicalCarryTruncationDiscrepancy
        (N := N) χ (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1)
        tu.1 tu.2
  let complete :=
    χ.cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) (primorial w) b R
      (fun q : SelectedCFZFormIndex e => q.1)
  let completion :=
    χ.cfzCanonicalCarryEulerCompletionDiscrepancy
      (N := N) (primorial w) b R
      (fun q : SelectedCFZFormIndex e => q.1)
  have hunrestricted :
      Integrable unrestricted (volume.prod volume) :=
    χ.integrable_pairedEnvelope_mul_cfzCanonicalCarryUnrestrictedFourierAverage
      (N := N) (primorial w) b hR e
  have htruncation :
      Integrable truncation (volume.prod volume) :=
    integrable_cfzCanonicalCarryTruncationDiscrepancy
      χ (primorial w) b hR
        (fun q : SelectedCFZFormIndex e => q.1)
  have hcomplete :
      Integrable complete (volume.prod volume) :=
    χ.integrable_cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) hk hbound hwb e hR
  have hcompletion :
      Integrable completion (volume.prod volume) :=
    χ.integrable_cfzCanonicalCarryEulerCompletionDiscrepancy
      (N := N) hk hbound hwb e hR
  have htruncationIntegral :
      (∫ tu, truncation tu ∂(volume.prod volume)) = 0 := by
    exact
      integral_cfzCanonicalCarryTruncationDiscrepancy_eq_zero
        χ (primorial w) b hR
          (fun q : SelectedCFZFormIndex e => q.1)
  have hcompletionIntegral :
      (∫ tu, completion tu ∂(volume.prod volume)) = 0 := by
    exact
      χ.integral_cfzCanonicalCarryEulerCompletionDiscrepancy_eq_zero
        (N := N) hk hbound hwb e hR
  have hunrestrictedIntegral :
      (∫ tu, unrestricted tu ∂(volume.prod volume)) =
        ∫ tu, complete tu ∂(volume.prod volume) := by
    have hsub :
        (∫ tu, unrestricted tu - complete tu
            ∂(volume.prod volume)) = 0 := by
      simpa [completion, unrestricted, complete,
        SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy]
        using hcompletionIntegral
    rw [integral_sub hunrestricted hcomplete] at hsub
    exact sub_eq_zero.mp hsub
  rw [
    χ.selectedCFZEulerFourierMainTerm_eq_integral_unrestricted_add_discrepancy
      (N := N) R (primorial w) b e]
  congr 2
  rw [integral_add hunrestricted htruncation,
    htruncationIntegral, add_zero, hunrestrictedIntegral]
