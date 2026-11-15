-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
-- name    : Wikipedia.SzemeredisTheorem.cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:35.899186+00:00
-- url     : https://prove2.me/theorems/9d9eb208-ee55-40ed-9c67-99e07680e547
-- title:
--   A paired cutoff zeta shift gives the archimedean kernel
-- statement:
--   Let $R>1$ be natural and let $t,u\in\mathbb R$. With $z_R(t)=(1-2\pi it)/\log R$,
--
--   $$
--   \frac{z_R(t)z_R(u)}{z_R(t)+z_R(u)}
--   =\frac1{\log R}\,
--   \frac{(1-2\pi it)(1-2\pi iu)}{2-2\pi i(t+u)}.
--   $$
--
--   The final quotient is the specified cutoff-normalizer kernel.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CutoffZetaSingularKernel.lean#L51-L92

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# The cutoff zeta pole as the normalizer kernel

For the Fourier shift

`z_R(t) = (1 - 2πit) / log R`,

the elementary pole contribution in one completed zeta quotient is

`z_R(t) z_R(u) / (z_R(t) + z_R(u))`.

This file identifies it exactly with `1 / log R` times the archimedean
kernel evaluated in `CutoffNormalizerIntegral`.  The identity is then
multiplied over a finite selected family and combined with both products of
cutoff Fourier transforms.  No limit is taken here: these are exact
algebraic normalization formulas.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
    {R : ℕ} (hR : 1 < R) (t u : ℝ) :
    (cutoffZetaShift R t *
          cutoffZetaShift R u) /
        (cutoffZetaShift R t +
          cutoffZetaShift R u) =
      (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
        SmoothSieveCutoff.cutoffNormalizerKernel t u := by sorry
