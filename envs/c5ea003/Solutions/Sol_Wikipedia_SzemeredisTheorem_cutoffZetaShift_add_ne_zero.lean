-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutoffZetaShift_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:31.421405+00:00
-- url     : https://prove2.me/submissions/587055ac-4669-43d1-b0d1-90c20bd393fd

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

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















/-! ## Finite Fourier systems -/









/-! ## The standard growing truncation box -/







end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology

open Wikipedia.SzemeredisTheorem in
theorem solution
    {R : ℕ} (hR : 1 < R) (t u : ℝ) :
    cutoffZetaShift R t +
        cutoffZetaShift R u ≠ 0 := by
  intro hzero
  have hre :
      0 <
        (cutoffZetaShift R t +
          cutoffZetaShift R u).re := by
    rw [Complex.add_re]
    exact add_pos
      (cutoffZetaShift_re_pos hR t)
      (cutoffZetaShift_re_pos hR u)
  rw [hzero] at hre
  norm_num at hre
