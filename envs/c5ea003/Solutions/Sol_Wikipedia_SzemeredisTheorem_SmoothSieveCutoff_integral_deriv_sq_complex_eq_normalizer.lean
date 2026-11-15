-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_deriv_sq_complex_eq_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:22:58.297579+00:00
-- url     : https://prove2.me/submissions/7e931830-1b19-48a1-99c8-161491fff495

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
/-- The positive-half-line integral of the complexified derivative
square is the real cutoff normalizer embedded in `ℂ`. -/
theorem solution
    (χ : SmoothSieveCutoff) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ)) =
      (χ.normalizer : ℂ) := by
  have hreal :
      (∫ x : ℝ in Set.Ioi (0 : ℝ),
          (deriv χ.toFun x) ^ 2) =
        χ.normalizer := by
    rw [normalizer]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change
        (deriv χ.toFun x) ^ 2 =
          |deriv χ.toFun x| ^ 2
      exact (sq_abs (deriv χ.toFun x)).symm
  calc
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ)) =
        ((show ℝ from
          ∫ x : ℝ in Set.Ioi (0 : ℝ),
            (deriv χ.toFun x) ^ 2) : ℂ) :=
      integral_ofReal
    _ = (χ.normalizer : ℂ) := by
      rw [hreal]
