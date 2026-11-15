-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_cutoff_eq_integral
-- name    : Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoff_eq_integral
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:34:59.06693+00:00
-- url     : https://prove2.me/theorems/cca95573-5988-4962-878d-775d7dd477cd
-- title:
--   Fourier inversion for a smooth sieve cutoff
-- statement:
--   For every smooth sieve cutoff $\chi$ and $x\in\mathbb R$, its complexified value is $\chi(x)=\int_{\mathbb R}\widehat\chi(t)\operatorname{cutoffMultiplicativePhase}(x,t)\,dt$, using the cutoff Fourier transform and multiplicative phase defined in the library.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothCutoffFourier.lean#L234-L266

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

theorem Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoff_eq_integral
    (χ : SmoothSieveCutoff) (x : ℝ) :
    (χ x : ℂ) =
      ∫ t : ℝ,
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t := by sorry
