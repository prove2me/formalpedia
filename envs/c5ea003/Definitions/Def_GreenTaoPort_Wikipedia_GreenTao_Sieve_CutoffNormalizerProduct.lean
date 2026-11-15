-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T08:57:20.692199+00:00
-- url     : https://prove2.me/theorems/e68db6ee-2fa7-4681-b8a0-f5d3ab80dc79
-- title:
--   Finite products of paired cutoff-normalizer factors
-- statement:
--   For a smooth cutoff $\chi$, let $F_\chi$ be the Fourier transform of $e^x\chi(x)$ and let $K(t,u)$ be the one-pair archimedean normalizer kernel. The paired factor is
--
--   $$
--   A_\chi(t,u)=F_\chi(t)F_\chi(u)K(t,u).
--   $$
--
--   For a finite index type, the bundle defines the product of these factors in two equivalent coordinate conventions: a family of pairs $(t_q,u_q)$, and a pair of real-valued families $(t,u)$. The definitions impose no truncation on the real frequencies; later integration results identify their archimedean contribution.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CutoffNormalizerProduct.lean#L33-L56

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Mathlib.MeasureTheory.Integral.Pi
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

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

namespace SmoothSieveCutoff

/-- The unabbreviated archimedean factor for one pair of Fourier
variables. -/
noncomputable def cutoffNormalizerPairFactor
    (χ : SmoothSieveCutoff) (z : ℝ × ℝ) : ℂ :=
  χ.cutoffFourierTransform z.1 *
    χ.cutoffFourierTransform z.2 *
    cutoffNormalizerKernel z.1 z.2

/-- The product of the one-pair archimedean factors over a finite selected
family, written with paired coordinates. -/
noncomputable def cutoffNormalizerPairedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (z : κ → ℝ × ℝ) : ℂ :=
  ∏ i, χ.cutoffNormalizerPairFactor (z i)

/-- The same finite product in the separated `(t,u)` coordinate convention
used by the multivariate Fourier divisor expansion. -/
noncomputable def cutoffNormalizerSeparatedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  ∏ i,
    χ.cutoffNormalizerPairFactor
      (tu.1 i, tu.2 i)













end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


