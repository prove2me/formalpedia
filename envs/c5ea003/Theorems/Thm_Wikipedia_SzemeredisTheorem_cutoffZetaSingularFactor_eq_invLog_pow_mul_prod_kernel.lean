-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaSingularFactor_eq_invLog_pow_mul_prod_kernel
-- name    : Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor_eq_invLog_pow_mul_prod_kernel
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:43.107202+00:00
-- url     : https://prove2.me/theorems/dd564209-32e3-44aa-a26d-e5227536b84a
-- title:
--   The singular zeta factor separates into logarithmic and kernel products
-- statement:
--   For a finite index type $K$ of size $m$, a natural $R>1$, and real families $t,u$,
--
--   $$
--   Z_{\rm sing}(R,t,u)
--   =(\log R)^{-m}\prod_{q\in K}K(t_q,u_q),
--   $$
--
--   where $K(t,u)=(1-2\pi it)(1-2\pi iu)/(2-2\pi i(t+u))$ is the cutoff-normalizer kernel.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CutoffZetaSingularKernel.lean#L94-L130

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

theorem Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor_eq_invLog_pow_mul_prod_kernel
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSingularFactor R t u =
      ((((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) ^
          Fintype.card κ) *
        ∏ i,
          SmoothSieveCutoff.cutoffNormalizerKernel
            (t i) (u i) := by sorry
