-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffDerivativeSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:22:58.32609+00:00
-- url     : https://prove2.me/submissions/36353adb-73d6-4f4b-87de-6df3e455be91

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

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Pointwise evaluation of the differentiated spatial Schwartz
function. -/
theorem solution
    (χ : SmoothSieveCutoff) (x : ℝ) :
    χ.cutoffDerivativeSchwartz x =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
  have hχdiff :
      DifferentiableAt ℝ χ.toFun x :=
    (χ.smooth.differentiable (by simp)).differentiableAt
  have hreal :
      HasDerivAt
        (Real.exp * χ.toFun)
        (Real.exp x * χ.toFun x +
          Real.exp x * deriv χ.toFun x) x := by
    simpa only [Pi.mul_apply, mul_comm, add_comm] using
      (Real.hasDerivAt_exp x).mul hχdiff.hasDerivAt
  have hcomplex :
      deriv χ.fourierInput x =
        ((Real.exp x * χ.toFun x +
          Real.exp x * deriv χ.toFun x : ℝ) : ℂ) := by
    change
      deriv
          (fun y : ℝ =>
            ((Real.exp y * χ.toFun y : ℝ) : ℂ)) x =
        _
    exact hreal.ofReal_comp.deriv
  rw [cutoffDerivativeSchwartz]
  change
    χ.fourierInput x -
        fderiv ℝ χ.fourierInput x (1 : ℝ) =
      -((Real.exp x * deriv χ.toFun x : ℝ) : ℂ)
  rw [fderiv_apply_one_eq_deriv, hcomplex]
  simp only [fourierInput]
  push_cast
  ring
