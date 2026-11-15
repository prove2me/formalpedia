-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_cutoffFourierTransform_mul_derivativeWeight_mul_character
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:05.463034+00:00
-- url     : https://prove2.me/submissions/b17f07ac-dbb3-4bde-b600-24fcdfbeb81a

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_cutoffDerivativeSchwartz_apply
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_fourier_cutoffDerivativeSchwartz_apply
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_schwartz_eq_integral_fourier_mul_inverseFourierCharacter

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# The archimedean cutoff normalizer integral

For Mathlib's analyst Fourier normalization, put

`F(t) = 𝓕 (x ↦ exp(x) χ(x))(t)`

and

`W(t) = 1 - 2 π i t`.

The one-pair archimedean factor in the Goldston--Yıldırım calculation is

`∫ t, ∫ u, F(t) F(u) W(t) W(u) /
  (2 - 2 π i (t + u))`.

This file identifies it with the derivative-square normalizer

`∫_{0 < x} |χ'(x)|² dx`.

The proof records both analytic ingredients explicitly.  First,
`W(t) F(t)` is the Fourier transform of
`x ↦ -exp(x) χ'(x)`.  Second, the reciprocal denominator is the Laplace
integral

`∫_{0 < x} exp((-2 + 2 π i (t + u))x) dx`.

The remaining argument is an absolutely convergent Fubini interchange.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Function MeasureTheory Set
open scoped BigOperators FourierTransform LineDeriv SchwartzMap

namespace SmoothSieveCutoff

/-! ## The differentiated Fourier input -/











/-- Ordinary-function version of
`fourier_cutoffDerivativeSchwartz_apply`. -/
theorem fourier_coe_cutoffDerivativeSchwartz_apply
    (χ : SmoothSieveCutoff) (t : ℝ) :
    𝓕 (χ.cutoffDerivativeSchwartz : ℝ → ℂ) t =
      χ.cutoffFourierTransform t *
        cutoffDerivativeFrequencyWeight t := by
  rw [← SchwartzMap.fourier_coe
    χ.cutoffDerivativeSchwartz]
  exact fourier_cutoffDerivativeSchwartz_apply χ t





/-! It is useful below to give the differentiated transform a short
name. -/











/-! ## The Laplace kernel -/



















/-! ## Absolute convergence of the three-variable integral -/









/-! ## Fubini and factorization -/















/-! ## The one-pair archimedean identity -/







end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# The archimedean cutoff normalizer integral

For Mathlib's analyst Fourier normalization, put

`F(t) = 𝓕 (x ↦ exp(x) χ(x))(t)`

and

`W(t) = 1 - 2 π i t`.

The one-pair archimedean factor in the Goldston--Yıldırım calculation is

`∫ t, ∫ u, F(t) F(u) W(t) W(u) /
  (2 - 2 π i (t + u))`.

This file identifies it with the derivative-square normalizer

`∫_{0 < x} |χ'(x)|² dx`.

The proof records both analytic ingredients explicitly.  First,
`W(t) F(t)` is the Fourier transform of
`x ↦ -exp(x) χ'(x)`.  Second, the reciprocal denominator is the Laplace
integral

`∫_{0 < x} exp((-2 + 2 π i (t + u))x) dx`.

The remaining argument is an absolutely convergent Fubini interchange.
-/
open Wikipedia.SzemeredisTheorem
open Filter Function MeasureTheory Set
open scoped BigOperators FourierTransform LineDeriv SchwartzMap
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff
/-! ## The differentiated Fourier input -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- The inverse transform of `W(t)F(t)` is
`-exp(x)χ'(x)`. -/
theorem solution
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (∫ t : ℝ,
        χ.cutoffFourierTransform t *
          cutoffDerivativeFrequencyWeight t *
            inverseFourierCharacter x t) =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
  rw [← χ.cutoffDerivativeSchwartz_apply x,
    schwartz_eq_integral_fourier_mul_inverseFourierCharacter
      χ.cutoffDerivativeSchwartz x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change
      χ.cutoffFourierTransform t *
            cutoffDerivativeFrequencyWeight t *
          inverseFourierCharacter x t =
        𝓕 (χ.cutoffDerivativeSchwartz : ℝ → ℂ) t *
          inverseFourierCharacter x t
    rw [fourier_coe_cutoffDerivativeSchwartz_apply]
