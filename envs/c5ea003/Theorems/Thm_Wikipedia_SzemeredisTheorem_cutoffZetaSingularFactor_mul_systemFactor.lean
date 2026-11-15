-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaSingularFactor_mul_systemFactor
-- name    : Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor_mul_systemFactor
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:37.238208+00:00
-- url     : https://prove2.me/theorems/97ba9119-0bd5-4b1b-8dce-5c9072132d67
-- title:
--   Singular and completed zeta factors recover the uncompleted ratio
-- statement:
--   Let $R>1$ be natural, let $K$ be finite, and let $t,u$ be real frequency families. Put $z_q=(1-2\pi it_q)/\log R$ and $v_q=(1-2\pi iu_q)/\log R$. Then
--
--   $$
--   Z_{\rm sing}(R,t,u)Z_{\rm comp}(R,t,u)
--   =\prod_{q\in K}\frac{\zeta(1+z_q+v_q)}{\zeta(1+z_q)\zeta(1+v_q)}.
--   $$
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ZetaEulerProductIdentification.lean#L124-L152

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
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
# Identifying the zeta-model Euler product

The model local factor attached to one pair of Fourier shifts `u,v` is

`(1 - p^(-1-u)) (1 - p^(-1-v)) / (1 - p^(-1-u-v))`.

Mathlib's Euler product for `riemannZeta` identifies its prime product with

`ζ(1+u+v) / (ζ(1+u) ζ(1+v))`

whenever the real parts of `u` and `v` are positive.  This file proves that
identity first for one pair and then for an arbitrary finite system.  It
then specializes to the exact Mathlib Fourier shifts and splits the answer
into the elementary singular factor and the removable completed factor from
`ZetaNearOne`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor_mul_systemFactor
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSingularFactor R t u *
        cutoffZetaSystemFactor R t u =
      ∏ i,
        riemannZeta
              (1 + cutoffZetaShift R (t i) +
                cutoffZetaShift R (u i)) /
          (riemannZeta
                (1 + cutoffZetaShift R (t i)) *
            riemannZeta
                (1 + cutoffZetaShift R (u i))) := by sorry
