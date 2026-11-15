-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_cutoffZetaShift_le_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:19:56.364211+00:00
-- url     : https://prove2.me/submissions/7f2e3348-a696-41f6-8649-be35c7b8f91f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_cutoffZetaShift_le

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
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
/-- Uniform shift bound on a truncated Fourier interval. -/
theorem solution
    {R : ℕ} (hR : 1 < R)
    {T t : ℝ} (ht : |t| ≤ T) :
    ‖cutoffZetaShift R t‖ ≤
      (1 + 2 * Real.pi * T) /
        Real.log R := by
  have hlog :
      0 ≤ Real.log (R : ℝ) :=
    (Real.log_pos (by exact_mod_cast hR)).le
  have hcoef :
      |2 * Real.pi * t| ≤
        2 * Real.pi * T := by
    calc
      |2 * Real.pi * t| =
          (2 * Real.pi) * |t| := by
        rw [abs_mul, abs_of_nonneg
          (mul_nonneg (by norm_num) Real.pi_pos.le)]
      _ ≤ (2 * Real.pi) * T :=
        mul_le_mul_of_nonneg_left ht
          (mul_nonneg (by norm_num) Real.pi_pos.le)
  have hnum :
      1 + |2 * Real.pi * t| ≤
        1 + 2 * Real.pi * T := by
    linarith
  exact (norm_cutoffZetaShift_le hR t).trans
    (div_le_div_of_nonneg_right
      hnum hlog)
