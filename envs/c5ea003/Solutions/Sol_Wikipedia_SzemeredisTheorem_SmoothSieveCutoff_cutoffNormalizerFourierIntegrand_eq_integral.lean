-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerFourierIntegrand_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:22:58.358475+00:00
-- url     : https://prove2.me/submissions/73779ad9-0d71-4028-a9d0-15b3f5d6380d

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

















/-! It is useful below to give the differentiated transform a short
name. -/











/-! ## The Laplace kernel -/







@[simp]
theorem cutoffNormalizerLaplaceExponent_re
    (t u : ℝ) :
    (cutoffNormalizerLaplaceExponent t u).re = -2 := by
  simp [cutoffNormalizerLaplaceExponent]

theorem cutoffNormalizerDenominator_eq_neg_exponent
    (t u : ℝ) :
    cutoffNormalizerDenominator t u =
      -cutoffNormalizerLaplaceExponent t u := by
  simp [cutoffNormalizerDenominator,
    cutoffNormalizerLaplaceExponent]
  ring



/-- Exact Laplace transform of the reciprocal denominator. -/
theorem integral_exp_cutoffNormalizerLaplaceExponent_Ioi
    (t u : ℝ) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        Complex.exp
          (cutoffNormalizerLaplaceExponent t u * x)) =
      (cutoffNormalizerDenominator t u)⁻¹ := by
  rw [integral_exp_mul_complex_Ioi
    (a := cutoffNormalizerLaplaceExponent t u)
    (by simp)]
  rw [cutoffNormalizerDenominator_eq_neg_exponent]
  simp [div_eq_mul_inv]





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
/-! It is useful below to give the differentiated transform a short
name. -/
/-! ## The Laplace kernel -/
/-! ## Absolute convergence of the three-variable integral -/
/-! ## Fubini and factorization -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Pointwise replacement of the reciprocal denominator by the
Laplace integral. -/
theorem solution
    (χ : SmoothSieveCutoff) (t u : ℝ) :
    χ.cutoffNormalizerFourierIntegrand t u =
      ∫ x : ℝ in Set.Ioi (0 : ℝ),
        χ.cutoffNormalizerTripleIntegrand
          (x, (t, u)) := by
  rw [cutoffNormalizerFourierIntegrand,
    div_eq_mul_inv,
    ← integral_exp_cutoffNormalizerLaplaceExponent_Ioi,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change
      χ.cutoffWeightedFourier t *
            χ.cutoffWeightedFourier u *
          Complex.exp
            (cutoffNormalizerLaplaceExponent t u * x) =
        Complex.exp
              (cutoffNormalizerLaplaceExponent t u * x) *
            χ.cutoffWeightedFourier t *
          χ.cutoffWeightedFourier u
    ring
