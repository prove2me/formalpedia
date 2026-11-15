-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoff_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:02:32.513869+00:00
-- url     : https://prove2.me/submissions/e6b8c06d-254e-43ce-a747-bab684807d02

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

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



















/-- The Fourier input is integrable. -/
theorem fourierInput_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.fourierInput := by
  change Integrable (χ.fourierInputSchwartz : ℝ → ℂ)
  exact χ.fourierInputSchwartz.integrable

/-- The cutoff transform is integrable, as needed for pointwise Fourier
inversion. -/
theorem cutoffFourierTransform_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffFourierTransform := by
  change Integrable (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.integrable















/-- Pointwise Fourier inversion for the exponentially weighted cutoff. -/
theorem fourierInput_eq_integral
    (χ : SmoothSieveCutoff) (x : ℝ) :
    χ.fourierInput x =
      ∫ t : ℝ,
        χ.cutoffFourierTransform t *
          inverseFourierCharacter x t := by
  have hinversion :
      𝓕⁻ (𝓕 χ.fourierInput) x = χ.fourierInput x :=
    χ.fourierInput_integrable.fourierInv_fourier_eq
      χ.cutoffFourierTransform_integrable
      χ.fourierInput_contDiff.continuous.continuousAt
  rw [Real.fourierInv_eq'] at hinversion
  symm
  simpa only [cutoffFourierTransform, inverseFourierCharacter,
    RCLike.inner_apply, conj_trivial, Complex.real_smul, smul_eq_mul,
    mul_comm] using hinversion



/-- The cutoff phase is the inverse Fourier character times the real
exponential `exp(-x)`. -/
theorem cutoffMultiplicativePhase_eq
    (x t : ℝ) :
    cutoffMultiplicativePhase x t =
      (Real.exp (-x) : ℂ) * inverseFourierCharacter x t := by
  simp only [cutoffMultiplicativePhase, inverseFourierCharacter,
    Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]



















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open Function MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators FourierTransform
  ContDiff SchwartzMap
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Pointwise Fourier inversion in the form used by the
Goldston--Yıldırım divisor sum. -/
theorem solution
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (χ x : ℂ) =
      ∫ t : ℝ,
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t := by
  calc
    (χ x : ℂ) =
        (Real.exp (-x) : ℂ) * χ.fourierInput x := by
          rw [fourierInput]
          push_cast
          rw [← mul_assoc, ← Complex.exp_add]
          simp
    _ = (Real.exp (-x) : ℂ) *
          ∫ t : ℝ,
            χ.cutoffFourierTransform t *
              inverseFourierCharacter x t := by
          rw [χ.fourierInput_eq_integral x]
    _ = ∫ t : ℝ,
          (Real.exp (-x) : ℂ) *
            (χ.cutoffFourierTransform t *
              inverseFourierCharacter x t) := by
          rw [integral_const_mul]
    _ = ∫ t : ℝ,
          χ.cutoffFourierTransform t *
            cutoffMultiplicativePhase x t := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun t ↦ by
            dsimp only
            rw [cutoffMultiplicativePhase_eq]
            ring
