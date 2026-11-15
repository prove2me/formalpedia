-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:54:27.51737+00:00
-- url     : https://prove2.me/theorems/40abea5f-e48b-44c6-b134-c4201995eb9b
-- title:
--   Archimedean Fourier kernels for the cutoff normalizer
-- statement:
--   Write $F_\chi=\mathcal F(e^x\chi(x))$ and $w(t)=1-2\pi it$. The differentiated Schwartz input is $g-g'=-e^x\chi'(x)$, and the weighted Fourier factor is $F_\chi(t)w(t)$. The one-pair kernel is
--
--   $$
--   K(t,u)=\frac{w(t)w(u)}{2-2\pi i(t+u)}.
--   $$
--
--   The bundle supplies the denominator, the Laplace exponent $-2+2\pi i(t+u)$, and the resulting two-variable Fourier integrand $F_\chi(t)F_\chi(u)K(t,u)$. Its triple-integrand version multiplies the two weighted Fourier factors by $\exp((-2+2\pi i(t+u))x)$, with variables ordered as $(x,(t,u))$. These definitions make the later Laplace representation and Fubini exchange explicit.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CutoffNormalizerIntegral.lean#L44-L453

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Lean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
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

namespace Wikipedia.SzemeredisTheorem

open Filter Function MeasureTheory Set
open scoped BigOperators FourierTransform LineDeriv SchwartzMap

namespace SmoothSieveCutoff

/-! ## The differentiated Fourier input -/

/-- The linear Fourier weight dictated by Mathlib's `2π` convention. -/
noncomputable def cutoffDerivativeFrequencyWeight (t : ℝ) : ℂ :=
  1 - ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I

/-- The differentiated spatial Schwartz function
`g - g' = -exp(x) χ'(x)`, where `g(x) = exp(x)χ(x)`. -/
noncomputable def cutoffDerivativeSchwartz
    (χ : SmoothSieveCutoff) : 𝓢(ℝ, ℂ) :=
  χ.fourierInputSchwartz -
    ∂_{(1 : ℝ)} χ.fourierInputSchwartz













/-! It is useful below to give the differentiated transform a short
name. -/

/-- The Fourier transform after applying the archimedean derivative
weight. -/
noncomputable def cutoffWeightedFourier
    (χ : SmoothSieveCutoff) (t : ℝ) : ℂ :=
  χ.cutoffFourierTransform t *
    cutoffDerivativeFrequencyWeight t









/-! ## The Laplace kernel -/

/-- The complex denominator of the one-pair archimedean kernel. -/
noncomputable def cutoffNormalizerDenominator
    (t u : ℝ) : ℂ :=
  2 -
    ((2 * Real.pi * (t + u) : ℝ) : ℂ) *
      Complex.I

/-- The one-pair Fourier kernel in Mathlib's analyst normalization. -/
noncomputable def cutoffNormalizerKernel
    (t u : ℝ) : ℂ :=
  cutoffDerivativeFrequencyWeight t *
      cutoffDerivativeFrequencyWeight u /
    cutoffNormalizerDenominator t u

/-- The exponent in the Laplace representation of the reciprocal
denominator. -/
noncomputable def cutoffNormalizerLaplaceExponent
    (t u : ℝ) : ℂ :=
  -2 +
    ((2 * Real.pi * (t + u) : ℝ) : ℂ) *
      Complex.I













/-! ## Absolute convergence of the three-variable integral -/

/-- The full integrand after replacing the reciprocal denominator by its
Laplace integral.  The variables are ordered as `x, (t,u)` to make the
Fubini exchange explicit. -/
noncomputable def cutoffNormalizerTripleIntegrand
    (χ : SmoothSieveCutoff)
    (z : ℝ × (ℝ × ℝ)) : ℂ :=
  Complex.exp
      (cutoffNormalizerLaplaceExponent z.2.1 z.2.2 * z.1) *
    χ.cutoffWeightedFourier z.2.1 *
    χ.cutoffWeightedFourier z.2.2







/-! ## Fubini and factorization -/

/-- The differentiated two-variable Fourier integrand. -/
noncomputable def cutoffNormalizerFourierIntegrand
    (χ : SmoothSieveCutoff) (t u : ℝ) : ℂ :=
  χ.cutoffWeightedFourier t *
      χ.cutoffWeightedFourier u /
    cutoffNormalizerDenominator t u













/-! ## The one-pair archimedean identity -/







end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffDerivativeFrequencyWeight.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffDerivativeSchwartz.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerDenominator.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerFourierIntegrand.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerKernel.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerLaplaceExponent.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffNormalizerTripleIntegrand.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffWeightedFourier.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


