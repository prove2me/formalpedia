-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_cutoffNormalizerTripleIntegrand_pair
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:22:58.532282+00:00
-- url     : https://prove2.me/submissions/925c3196-6064-4fa1-9ca5-0fc8f74d8b5f

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
/-- At fixed positive-half-line parameter, the two Fourier variables
factor into the square of one inverse transform. -/
theorem solution
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerTripleIntegrand
          (x, z) ∂(volume.prod volume)) =
      (Real.exp (-2 * x) : ℂ) *
        (∫ t : ℝ,
          χ.cutoffWeightedFourier t *
            inverseFourierCharacter x t) ^ 2 := by
  calc
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerTripleIntegrand
          (x, z) ∂(volume.prod volume)) =
        ∫ z : ℝ × ℝ,
          (Real.exp (-2 * x) : ℂ) *
            ((χ.cutoffWeightedFourier z.1 *
                inverseFourierCharacter x z.1) *
              (χ.cutoffWeightedFourier z.2 *
                inverseFourierCharacter x z.2))
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change
          Complex.exp
                (cutoffNormalizerLaplaceExponent z.1 z.2 * x) *
              χ.cutoffWeightedFourier z.1 *
              χ.cutoffWeightedFourier z.2 =
            _
        rw [exp_cutoffNormalizerLaplaceExponent_mul_eq]
        ring
    _ =
        (Real.exp (-2 * x) : ℂ) *
          ∫ z : ℝ × ℝ,
            (χ.cutoffWeightedFourier z.1 *
              inverseFourierCharacter x z.1) *
            (χ.cutoffWeightedFourier z.2 *
              inverseFourierCharacter x z.2)
            ∂(volume.prod volume) := by
      exact integral_const_mul
        (Real.exp (-2 * x) : ℂ)
        (fun z : ℝ × ℝ =>
          (χ.cutoffWeightedFourier z.1 *
              inverseFourierCharacter x z.1) *
            (χ.cutoffWeightedFourier z.2 *
              inverseFourierCharacter x z.2))
    _ =
        (Real.exp (-2 * x) : ℂ) *
          (∫ t : ℝ,
            χ.cutoffWeightedFourier t *
              inverseFourierCharacter x t) ^ 2 := by
      rw [integral_prod_mul
        (fun t : ℝ =>
          χ.cutoffWeightedFourier t *
            inverseFourierCharacter x t)
        (fun u : ℝ =>
          χ.cutoffWeightedFourier u *
            inverseFourierCharacter x u)]
      ring
