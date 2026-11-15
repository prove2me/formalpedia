-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.tendsto_norm_integral_selectedCFZCanonicalArchimedeanBaseline_compl_sqrt_log
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.151765+00:00
-- url     : https://prove2.me/submissions/2b15c44b-b077-4841-960c-0599bcea998f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integrable_cutoffNormalizerSeparatedProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_integral_selectedCFZPairedFourierBox_compl_atTop

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













/-- The conventional Fourier-box radius tends to infinity. -/
theorem tendsto_sqrt_log_nat_atTop :
    Tendsto
      (fun R : ℕ => Real.sqrt (Real.log R))
      atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)





end SmoothSieveCutoff

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

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- The fixed archimedean baseline has vanishing complementary integral
along every sieve-radius sequence tending to infinity. -/
theorem
    solution
    {k : ℕ} (χ : SmoothSieveCutoff)
    (Rseq : ℕ → ℕ)
    (hRseq : Tendsto Rseq atTop atTop)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun n : ℕ =>
        ‖∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e
              (Real.sqrt (Real.log (Rseq n))))ᶜ,
          χ.selectedCFZCanonicalArchimedeanBaseline e tu
          ∂(volume.prod volume)‖)
      atTop (𝓝 0) := by
  have hintegral :
      Tendsto
        (fun n : ℕ =>
          ∫ tu in
              (SmoothSieveCutoff.selectedCFZPairedFourierBox e
                (Real.sqrt (Real.log (Rseq n))))ᶜ,
            χ.selectedCFZCanonicalArchimedeanBaseline e tu
            ∂(volume.prod volume))
        atTop (𝓝 0) :=
    (tendsto_integral_selectedCFZPairedFourierBox_compl_atTop e
      (χ.integrable_selectedCFZCanonicalArchimedeanBaseline e)).comp
        (SmoothSieveCutoff.tendsto_sqrt_log_nat_atTop.comp hRseq)
  simpa using hintegral.norm
