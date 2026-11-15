-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.norm_selectedCFZCanonicalEulerFourierMainTerm_sub_one_le_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:06:00.40244+00:00
-- url     : https://prove2.me/submissions/43206965-bf7a-4df1-a3a2-6dc9cc756e16

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integrable_cutoffNormalizerSeparatedProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_selectedCFZCanonicalArchimedeanBaseline_eq_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_selectedCFZCanonicalEulerFourierMainTerm_eq_completeEulerIntegral

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
# Exact W-tricked Fourier normalization

The normalized Selberg majorant contributes, for every selected form,

`(φ(W) / W) / (cχ log R)` and `(log R)²`.

The elementary pole in the zeta quotient contributes `(log R)⁻¹`, while
the omitted primes dividing the primorial contribute the inverse
reduced-residue density.  This file records the exact cancellation:

`Selberg scale × (log R)² × zeta pole × small-prime correction`

is

`cχ⁻¹ × cutoff-normalizer kernel × normalized small-prime residual`.

The identity is pointwise in all Fourier variables.  Specializing
`cχ` to the derivative-square normalizer and replacing the two correction
factors by one leaves an integrand whose full integral is exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators







/-- The normalized archimedean baseline is absolutely integrable. -/
theorem
    SmoothSieveCutoff.integrable_invNormalizerPow_mul_cutoffNormalizerSeparatedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (fun tu : (κ → ℝ) × (κ → ℝ) =>
        ((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ *
          χ.cutoffNormalizerSeparatedProduct tu)
      (volume.prod volume) :=
  χ.integrable_cutoffNormalizerSeparatedProduct.const_mul
    (((χ.normalizer : ℂ)⁻¹) ^ Fintype.card κ)



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







/-! ## Scaled integrand and normalized archimedean baseline -/





/-- The scaled complete integrand is integrable. -/
theorem
    SmoothSieveCutoff.integrable_selectedCFZCanonicalCompleteEulerScaledIntegrand
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
      (χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
        (N := N) w b R e)
      (volume.prod volume) := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
  exact
    (χ.integrable_cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) hk hbound hwb e hR).const_mul _
      |>.const_mul _

/-- The normalized archimedean baseline is integrable. -/
theorem
    SmoothSieveCutoff.integrable_selectedCFZCanonicalArchimedeanBaseline
    {k : ℕ} (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) :
    Integrable
      (χ.selectedCFZCanonicalArchimedeanBaseline e)
      (volume.prod volume) := by
  change
    Integrable
      (fun tu =>
        ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex e) *
          χ.cutoffNormalizerSeparatedProduct tu)
      (volume.prod volume)
  exact
    χ.integrable_invNormalizerPow_mul_cutoffNormalizerSeparatedProduct
      (κ := SelectedCFZFormIndex e)



/-- Pointwise scaling commutes with the full integral. -/
theorem
    SmoothSieveCutoff.integral_selectedCFZCanonicalCompleteEulerScaledIntegrand
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) :
    (∫ tu :
        (SelectedCFZFormIndex e → ℝ) ×
          (SelectedCFZFormIndex e → ℝ),
      χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
        (N := N) w b R e tu
      ∂(volume.prod volume)) =
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
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
  rw [integral_const_mul, integral_const_mul]

/-- The exact complete-main-term identity with all scalar factors moved
inside the integral. -/
theorem
    SmoothSieveCutoff.selectedCFZEulerFourierMainTerm_eq_integral_completeScaledIntegrand
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
      ∫ tu :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ),
        χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
          (N := N) w b R e tu
        ∂(volume.prod volume) := by
  rw [
    χ.selectedCFZCanonicalEulerFourierMainTerm_eq_completeEulerIntegral
      (N := N) hk hbound hwb e hR,
    χ.integral_selectedCFZCanonicalCompleteEulerScaledIntegrand
      (N := N) w b R e]

/-- Any integrable function splits exactly into the selected Fourier box
and its complement. -/
theorem integral_eq_selectedCFZPairedFourierBox_add_compl
    {k : ℕ} (e : LinearFormsExponent k)
    (T : ℝ)
    {f :
      ((SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    (∫ tu, f tu ∂(volume.prod volume)) =
      (∫ tu in SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
          f tu ∂(volume.prod volume)) +
        ∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
          f tu ∂(volume.prod volume) := by
  exact
    (integral_add_compl
      (SmoothSieveCutoff.measurableSet_selectedCFZPairedFourierBox e T) hf).symm



/-- The complete-model complementary-box norm is exactly the tail norm
controlled by `CFZCanonicalEulerCompletionTail`. -/
theorem
    SmoothSieveCutoff.norm_integral_selectedCFZCanonicalCompleteEulerScaledIntegrand_compl_eq
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (w b R : ℕ) (e : LinearFormsExponent k) (T : ℝ) :
    ‖∫ tu in
        (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
        χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
          (N := N) w b R e tu
        ∂(volume.prod volume)‖ =
      χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
        (N := N) w b R e T := by
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledIntegrand
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledTailNorm
  rw [integral_const_mul, integral_const_mul]



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
/-! ## Scaled integrand and normalized archimedean baseline -/
/-! ## Interior comparison and the complete integration estimate -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Quantitative bridge from a pointwise interior comparison to the whole
complete main term.  The two complementary contributions are kept in their
exact norms so that the schedule-uniform completion theorem can consume
the first one directly. -/
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
    {R : ℕ} (hR : 2 ≤ R)
    {δ T : ℝ} (hδ : 0 ≤ δ)
    (hinterior :
      ∀ tu ∈ SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
        ‖χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
              (N := N) w b R e tu -
            χ.selectedCFZCanonicalArchimedeanBaseline e tu‖ ≤
          δ *
            ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖) :
    ‖χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e - 1‖ ≤
      δ *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            ‖χ.selectedCFZCanonicalArchimedeanBaseline e tu‖
            ∂(volume.prod volume) +
        χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
          (N := N) w b R e T +
        ‖∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume)‖ := by
  let scaled :=
    χ.selectedCFZCanonicalCompleteEulerScaledIntegrand
      (N := N) w b R e
  let baseline :=
    χ.selectedCFZCanonicalArchimedeanBaseline e
  let box := SmoothSieveCutoff.selectedCFZPairedFourierBox e T
  have hscaled :
      Integrable scaled (volume.prod volume) :=
    χ.integrable_selectedCFZCanonicalCompleteEulerScaledIntegrand
      (N := N) hk hbound hwb e hR
  have hbaseline :
      Integrable baseline (volume.prod volume) :=
    χ.integrable_selectedCFZCanonicalArchimedeanBaseline e
  have hboxDifference :
      ‖∫ tu in box, scaled tu - baseline tu
          ∂(volume.prod volume)‖ ≤
        δ *
          ∫ tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ),
            ‖baseline tu‖ ∂(volume.prod volume) := by
    have hdom :
        ∀ᵐ tu ∂(volume.prod volume).restrict box,
          ‖scaled tu - baseline tu‖ ≤
            δ * ‖baseline tu‖ :=
      ae_restrict_of_forall_mem
        (SmoothSieveCutoff.measurableSet_selectedCFZPairedFourierBox e T)
        (fun tu htu => hinterior tu htu)
    have hboundIntegrable :
        Integrable
          (fun tu :
              (SelectedCFZFormIndex e → ℝ) ×
                (SelectedCFZFormIndex e → ℝ) =>
            δ * ‖baseline tu‖)
          (volume.prod volume) :=
      hbaseline.norm.const_mul δ
    have hnorm :=
      norm_integral_le_of_norm_le
        hboundIntegrable.integrableOn hdom
    have hsetLe :
        (∫ tu in box,
            δ * ‖baseline tu‖
            ∂(volume.prod volume)) ≤
          δ *
            ∫ tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ),
              ‖baseline tu‖ ∂(volume.prod volume) := by
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ hδ
      exact setIntegral_le_integral
        hbaseline.norm
        (ae_of_all _ fun tu => norm_nonneg _)
    exact hnorm.trans hsetLe
  have hboxSub :
      (∫ tu in box, scaled tu ∂(volume.prod volume)) -
          ∫ tu in box, baseline tu ∂(volume.prod volume) =
        ∫ tu in box, scaled tu - baseline tu
          ∂(volume.prod volume) := by
    symm
    exact integral_sub hscaled.integrableOn hbaseline.integrableOn
  have hmain :
      χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e =
        (∫ tu in box, scaled tu ∂(volume.prod volume)) +
          ∫ tu in boxᶜ, scaled tu
            ∂(volume.prod volume) := by
    rw [
      χ.selectedCFZEulerFourierMainTerm_eq_integral_completeScaledIntegrand
        (N := N) hk hbound hwb e hR]
    exact integral_eq_selectedCFZPairedFourierBox_add_compl
      e T hscaled
  have hbase :
      (1 : ℂ) =
        (∫ tu in box, baseline tu ∂(volume.prod volume)) +
          ∫ tu in boxᶜ, baseline tu
            ∂(volume.prod volume) := by
    rw [← χ.integral_selectedCFZCanonicalArchimedeanBaseline_eq_one e]
    exact integral_eq_selectedCFZPairedFourierBox_add_compl
      e T hbaseline
  calc
    ‖χ.selectedCFZCanonicalEulerFourierMainTerm
          (N := N) R (primorial w) b e - 1‖ =
        ‖((∫ tu in box, scaled tu ∂(volume.prod volume)) -
            ∫ tu in box, baseline tu ∂(volume.prod volume)) +
          ((∫ tu in boxᶜ, scaled tu ∂(volume.prod volume)) -
            ∫ tu in boxᶜ, baseline tu
              ∂(volume.prod volume))‖ := by
      rw [hmain, hbase]
      congr 1
      ring
    _ ≤
        ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
            ∫ tu in box, baseline tu ∂(volume.prod volume)‖ +
          ‖∫ tu in boxᶜ, scaled tu
            ∂(volume.prod volume)‖ +
          ‖∫ tu in boxᶜ, baseline tu
            ∂(volume.prod volume)‖ := by
      calc
        _ ≤
            ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
                ∫ tu in box, baseline tu ∂(volume.prod volume)‖ +
              ‖(∫ tu in boxᶜ, scaled tu ∂(volume.prod volume)) -
                ∫ tu in boxᶜ, baseline tu
                  ∂(volume.prod volume)‖ :=
          norm_add_le _ _
        _ ≤
            ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
                ∫ tu in box, baseline tu ∂(volume.prod volume)‖ +
              (‖∫ tu in boxᶜ, scaled tu
                  ∂(volume.prod volume)‖ +
                ‖∫ tu in boxᶜ, baseline tu
                  ∂(volume.prod volume)‖) :=
          add_le_add_right
            (norm_sub_le
              (∫ tu in boxᶜ, scaled tu
                ∂(volume.prod volume))
              (∫ tu in boxᶜ, baseline tu
                ∂(volume.prod volume)))
            ‖(∫ tu in box, scaled tu ∂(volume.prod volume)) -
                ∫ tu in box, baseline tu
                  ∂(volume.prod volume)‖
        _ = _ := (add_assoc _ _ _).symm
    _ ≤
        δ *
            ∫ tu :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ),
              ‖baseline tu‖ ∂(volume.prod volume) +
          χ.selectedCFZCanonicalCompleteEulerScaledTailNorm
            (N := N) w b R e T +
          ‖∫ tu in boxᶜ, baseline tu
            ∂(volume.prod volume)‖ := by
      rw [hboxSub,
        χ.norm_integral_selectedCFZCanonicalCompleteEulerScaledIntegrand_compl_eq
          (N := N) w b R e T]
      linarith
