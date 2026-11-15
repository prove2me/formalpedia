-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerTripleIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:34:18.462127+00:00
-- url     : https://prove2.me/submissions/478ac3b1-9e6c-4895-9a96-423668a0e49e

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integrable_cutoffFourierTransform_mul_derivativeWeight

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























/-- The cutoff transform is continuous. -/
theorem cutoffFourierTransform_continuous (χ : SmoothSieveCutoff) :
    Continuous χ.cutoffFourierTransform := by
  change Continuous (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.continuous







@[simp]
theorem norm_inverseFourierCharacter (x t : ℝ) :
    ‖inverseFourierCharacter x t‖ = 1 := by
  rw [inverseFourierCharacter, Complex.norm_exp]
  simp





























end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

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

















/-! It is useful below to give the differentiated transform a short
name. -/



theorem cutoffWeightedFourier_integrable
    (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffWeightedFourier := by
  change Integrable
    (fun t : ℝ =>
      χ.cutoffFourierTransform t *
        cutoffDerivativeFrequencyWeight t)
  exact χ.integrable_cutoffFourierTransform_mul_derivativeWeight

theorem cutoffWeightedFourier_continuous
    (χ : SmoothSieveCutoff) :
    Continuous χ.cutoffWeightedFourier := by
  apply χ.cutoffFourierTransform_continuous.mul
  unfold cutoffDerivativeFrequencyWeight
  fun_prop





/-! ## The Laplace kernel -/











/-- Split the Laplace phase into its decaying real factor and the two
unitary inverse-Fourier characters. -/
theorem exp_cutoffNormalizerLaplaceExponent_mul_eq
    (t u x : ℝ) :
    Complex.exp
        (cutoffNormalizerLaplaceExponent t u * x) =
      (Real.exp (-2 * x) : ℂ) *
        inverseFourierCharacter x t *
        inverseFourierCharacter x u := by
  rw [inverseFourierCharacter, inverseFourierCharacter,
    Complex.ofReal_exp, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  simp [cutoffNormalizerLaplaceExponent]
  ring







/-! ## Absolute convergence of the three-variable integral -/



theorem cutoffNormalizerTripleIntegrand_continuous
    (χ : SmoothSieveCutoff) :
    Continuous χ.cutoffNormalizerTripleIntegrand := by
  unfold cutoffNormalizerTripleIntegrand
  apply Continuous.mul
  · apply Continuous.mul
    · apply Complex.continuous_exp.comp
      unfold cutoffNormalizerLaplaceExponent
      fun_prop
    · exact
        χ.cutoffWeightedFourier_continuous.comp
          continuous_snd.fst
  · exact
      χ.cutoffWeightedFourier_continuous.comp
        continuous_snd.snd

/-- Exact factorization of the norm of the three-variable integrand. -/
theorem norm_cutoffNormalizerTripleIntegrand
    (χ : SmoothSieveCutoff)
    (z : ℝ × (ℝ × ℝ)) :
    ‖χ.cutoffNormalizerTripleIntegrand z‖ =
      Real.exp (-2 * z.1) *
        ‖χ.cutoffWeightedFourier z.2.1‖ *
        ‖χ.cutoffWeightedFourier z.2.2‖ := by
  rw [cutoffNormalizerTripleIntegrand,
    exp_cutoffNormalizerLaplaceExponent_mul_eq,
    norm_mul, norm_mul, norm_mul, norm_mul,
    norm_inverseFourierCharacter,
    norm_inverseFourierCharacter]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_one]



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
/-! It is useful below to give the differentiated transform a short
name. -/
/-! ## The Laplace kernel -/
/-! ## Absolute convergence of the three-variable integral -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Absolute integrability on the positive Laplace half-line times the
two Fourier lines. -/
theorem solution
    (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffNormalizerTripleIntegrand
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod
        (volume.prod volume)) := by
  have hx :
      Integrable
        (fun x : ℝ => Real.exp (-2 * x))
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
    simpa only [IntegrableOn] using
      (integrableOn_exp_mul_Ioi
        (a := (-2 : ℝ)) (by norm_num) 0)
  have htu :
      Integrable
        (fun z : ℝ × ℝ =>
          ‖χ.cutoffWeightedFourier z.1‖ *
            ‖χ.cutoffWeightedFourier z.2‖)
        (volume.prod volume) :=
    χ.cutoffWeightedFourier_integrable.norm.mul_prod
      χ.cutoffWeightedFourier_integrable.norm
  have hmajor :
      Integrable
        (fun z : ℝ × (ℝ × ℝ) =>
          Real.exp (-2 * z.1) *
            (‖χ.cutoffWeightedFourier z.2.1‖ *
              ‖χ.cutoffWeightedFourier z.2.2‖))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod
          (volume.prod volume)) :=
    hx.mul_prod htu
  refine
    (integrable_norm_iff
      χ.cutoffNormalizerTripleIntegrand_continuous.aestronglyMeasurable).mp ?_
  exact hmajor.congr
    (Filter.Eventually.of_forall fun z => by
      change
        Real.exp (-2 * z.1) *
              (‖χ.cutoffWeightedFourier z.2.1‖ *
                ‖χ.cutoffWeightedFourier z.2.2‖) =
          ‖χ.cutoffNormalizerTripleIntegrand z‖
      rw [norm_cutoffNormalizerTripleIntegrand]
      ring)
