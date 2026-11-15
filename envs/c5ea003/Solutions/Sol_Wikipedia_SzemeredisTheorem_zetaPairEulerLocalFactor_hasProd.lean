-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.zetaPairEulerLocalFactor_hasProd
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:15.945357+00:00
-- url     : https://prove2.me/submissions/fd2b4b1e-fce9-4aa4-acd1-04e9420c18e3

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

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Direct (rather than inverse) local Euler factor for the zeta function. -/
theorem riemannZeta_directEulerProduct_hasProd
    {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun p : Nat.Primes =>
        1 - (p : ℂ) ^ (-s))
      (riemannZeta s)⁻¹ := by
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have h := riemannZeta_eulerProduct_hasProd hs
  unfold HasProd at h ⊢
  simpa only [Finset.prod_inv_distrib, inv_inv] using
    h.inv₀ hz

















end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- Euler-product identification for one pair of positive-real-part shifts.
-/
theorem solution
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    HasProd
      (zetaPairEulerLocalFactor u v)
      (riemannZeta (1 + u + v) /
        (riemannZeta (1 + u) *
          riemannZeta (1 + v))) := by
  have hu1 : 1 < (1 + u).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hv1 : 1 < (1 + v).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have huv1 : 1 < (1 + u + v).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h :=
    ((riemannZeta_directEulerProduct_hasProd hu1).mul
      (riemannZeta_directEulerProduct_hasProd hv1)).mul
      (riemannZeta_eulerProduct_hasProd huv1)
  convert h using 1
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring
