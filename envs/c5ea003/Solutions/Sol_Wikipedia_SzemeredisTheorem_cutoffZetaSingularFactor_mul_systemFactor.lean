-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor_mul_systemFactor
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:05.767017+00:00
-- url     : https://prove2.me/submissions/c7e34137-569e-4427-ad4f-2bb224c5d959

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaShift_add_ne_zero
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaSystemFactor_eq_prod

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier parameters for the zeta comparison

`SmoothCutoffFourier` fixes Mathlib's analyst normalization.  Its divisor
phase is

`exp (-x + 2 π i t x)`, where `x = log d / log R`.

Thus the exact complex shift occurring in the Euler and zeta factors is

`(1 - 2 π i t) / log R`.

This file records that conversion, its positivity and elementary norm
bounds, and the resulting access to the completed zeta estimates.  Keeping
this bridge explicit prevents a hidden `2π` or sign error when the
multivariate Fourier integral is assembled.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology



theorem cutoffZetaShift_re
    (R : ℕ) (t : ℝ) :
    (cutoffZetaShift R t).re =
      1 / Real.log R := by
  change
    (Complex.ofReal ((Real.log (R : ℝ))⁻¹) *
      ((1 : ℂ) -
        Complex.ofReal (2 * Real.pi * t) *
          Complex.I)).re =
      1 / Real.log R
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.sub_re, Complex.one_re,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero]
  rw [one_div]
  simp

theorem cutoffZetaShift_re_pos
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    0 < (cutoffZetaShift R t).re := by
  rw [cutoffZetaShift_re R]
  exact one_div_pos.mpr
    (Real.log_pos (by exact_mod_cast hR))

theorem cutoffZetaShift_ne_zero
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    cutoffZetaShift R t ≠ 0 := by
  intro hzero
  have hre := cutoffZetaShift_re_pos hR t
  rw [hzero] at hre
  norm_num at hre













/-! ## Finite Fourier systems -/









/-! ## The standard growing truncation box -/







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
/-- Exact splitting of the finite zeta quotient into its elementary
singular factor and removable completed factor. -/
theorem solution
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
                (1 + cutoffZetaShift R (u i))) := by
  classical
  rw [cutoffZetaSingularFactor,
    cutoffZetaSystemFactor_eq_prod hR,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have ht :=
    cutoffZetaShift_ne_zero hR (t i)
  have hu :=
    cutoffZetaShift_ne_zero hR (u i)
  have hsum :=
    cutoffZetaShift_add_ne_zero hR (t i) (u i)
  field_simp
