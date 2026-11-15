-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integrable_cutoffNormalizerSeparatedProduct
-- name    : Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integrable_cutoffNormalizerSeparatedProduct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:37:16.468757+00:00
-- url     : https://prove2.me/theorems/81d14c42-faad-494a-b589-98bf40eca586
-- title:
--   Integrability of the separated normalizer product
-- statement:
--   For every finite index type $\kappa$ and smooth sieve cutoff $\chi$, the separated cutoff-normalizer product is integrable on $(\kappa\to\mathbb R)\times(\kappa\to\mathbb R)$ for product Lebesgue measure.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CutoffNormalizerProduct.lean#L124-L158

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
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
# Finite products of the cutoff-normalizer integral

The one-pair archimedean calculation in
`CutoffNormalizerIntegral` is the factor which remains for each selected
linear form after the arithmetic Euler product has been replaced by its
zeta model.  This file tensors that calculation over an arbitrary finite
family.

Both useful coordinate arrangements are recorded:

* a function `κ → ℝ × ℝ`, which makes the integrand a literal product of
  one-pair factors; and
* the sieve convention `(κ → ℝ) × (κ → ℝ)`, with the two copies of the
  Fourier variables separated.

The passage between them uses Mathlib's measure-preserving equivalence
between functions into a product and pairs of functions.  Thus the final
identity has exactly the product measure used by the multivariate divisor
expansion.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff

theorem Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integrable_cutoffNormalizerSeparatedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (χ.cutoffNormalizerSeparatedProduct :
        ((κ → ℝ) × (κ → ℝ)) → ℂ)
      (volume.prod volume) := by sorry
