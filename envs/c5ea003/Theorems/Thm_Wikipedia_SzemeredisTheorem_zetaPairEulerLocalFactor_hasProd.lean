-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_zetaPairEulerLocalFactor_hasProd
-- name    : Wikipedia.SzemeredisTheorem.zetaPairEulerLocalFactor_hasProd
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:01.678481+00:00
-- url     : https://prove2.me/theorems/e7d927ae-08f6-4e09-bb0a-748ccbf18ee9
-- title:
--   The paired zeta Euler product
-- statement:
--   For complex shifts $u,v$ with positive real parts, the prime-indexed paired zeta local factors have Euler product $\zeta(1+u+v)/(\zeta(1+u)\zeta(1+v))$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ZetaEulerProductIdentification.lean#L47-L73

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

theorem Wikipedia.SzemeredisTheorem.zetaPairEulerLocalFactor_hasProd
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    HasProd
      (zetaPairEulerLocalFactor u v)
      (riemannZeta (1 + u + v) /
        (riemannZeta (1 + u) *
          riemannZeta (1 + v))) := by sorry
