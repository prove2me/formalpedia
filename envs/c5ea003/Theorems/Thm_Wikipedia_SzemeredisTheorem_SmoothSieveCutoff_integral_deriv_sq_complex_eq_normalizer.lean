-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_deriv_sq_complex_eq_normalizer
-- name    : Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_deriv_sq_complex_eq_normalizer
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:37:21.427765+00:00
-- url     : https://prove2.me/theorems/9ace33bd-05fd-44fc-8e3c-356af864e38a
-- title:
--   The derivative-square integral equals the cutoff normalizer
-- statement:
--   For every smooth sieve cutoff $\chi$, the integral over $x>0$ of the complexified derivative square $\chi^{\prime}(x)^2$ equals the real cutoff normalizer embedded into $\mathbb C$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CutoffNormalizerIntegral.lean#L610-L636

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

theorem Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_deriv_sq_complex_eq_normalizer
    (χ : SmoothSieveCutoff) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (((deriv χ.toFun x) ^ 2 : ℝ) : ℂ)) =
      (χ.normalizer : ℂ) := by sorry
