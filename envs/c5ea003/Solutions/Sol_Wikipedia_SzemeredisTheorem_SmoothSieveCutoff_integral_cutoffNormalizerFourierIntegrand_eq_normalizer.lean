-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_cutoffNormalizerFourierIntegrand_eq_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:41:57.980397+00:00
-- url     : https://prove2.me/submissions/47d684d1-992c-4e62-ae62-a391fbd5b3a5

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_cutoffNormalizerFourierIntegrand_eq_integral
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_cutoffNormalizerTripleIntegrand_integrable
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_cutoffNormalizerTripleIntegrand_pair_eq_deriv_sq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_deriv_sq_complex_eq_normalizer

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
/-! ## The one-pair archimedean identity -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Product-measure form of the one-pair archimedean identity. -/
theorem solution
    (χ : SmoothSieveCutoff) :
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerFourierIntegrand
          z.1 z.2 ∂(volume.prod volume)) =
      (χ.normalizer : ℂ) := by
  calc
    (∫ z : ℝ × ℝ,
        χ.cutoffNormalizerFourierIntegrand
          z.1 z.2 ∂(volume.prod volume)) =
        ∫ z : ℝ × ℝ,
          (∫ x : ℝ in Set.Ioi (0 : ℝ),
            χ.cutoffNormalizerTripleIntegrand
              (x, z))
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        χ.cutoffNormalizerFourierIntegrand_eq_integral
          z.1 z.2
    _ =
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
          (∫ z : ℝ × ℝ,
            χ.cutoffNormalizerTripleIntegrand
              (x, z) ∂(volume.prod volume)) := by
      have htriple :
          Integrable
            (Function.uncurry
              (fun x : ℝ => fun z : ℝ × ℝ =>
                χ.cutoffNormalizerTripleIntegrand
                  (x, z)))
            ((volume.restrict (Set.Ioi (0 : ℝ))).prod
              (volume.prod volume)) := by
        exact
          χ.cutoffNormalizerTripleIntegrand_integrable.congr
            (Filter.Eventually.of_forall fun z => by
              change
                χ.cutoffNormalizerTripleIntegrand z =
                  χ.cutoffNormalizerTripleIntegrand
                    (z.1, z.2)
              rw [Prod.eta])
      exact
        (integral_integral_swap
          htriple).symm
    _ =
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
          (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        χ.integral_cutoffNormalizerTripleIntegrand_pair_eq_deriv_sq x
    _ = (χ.normalizer : ℂ) :=
      χ.integral_deriv_sq_complex_eq_normalizer
