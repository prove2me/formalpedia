-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_cutoffZetaShift_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:46.310037+00:00
-- url     : https://prove2.me/submissions/1568b99d-6e14-408e-9ccb-2d33df273cb9

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
/-- Elementary norm bound for the exact Fourier shift. -/
theorem solution
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    ‖cutoffZetaShift R t‖ ≤
      (1 + |2 * Real.pi * t|) /
        Real.log R := by
  have hlog :
      0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  calc
    ‖cutoffZetaShift R t‖ =
        (Real.log (R : ℝ))⁻¹ *
          ‖(1 : ℂ) -
            ((2 * Real.pi * t : ℝ) : ℂ) *
              Complex.I‖ := by
      rw [cutoffZetaShift, norm_mul,
        Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hlog)]
    _ ≤
        (Real.log (R : ℝ))⁻¹ *
          (1 + |2 * Real.pi * t|) := by
      apply mul_le_mul_of_nonneg_left
      · calc
          ‖(1 : ℂ) -
              ((2 * Real.pi * t : ℝ) : ℂ) *
                Complex.I‖ ≤
              ‖(1 : ℂ)‖ +
                ‖((2 * Real.pi * t : ℝ) : ℂ) *
                  Complex.I‖ :=
            norm_sub_le _ _
          _ = 1 + |2 * Real.pi * t| := by
            rw [norm_mul, Complex.norm_real,
              Real.norm_eq_abs,
              Complex.norm_I, mul_one, norm_one]
      · exact (inv_nonneg.mpr hlog.le)
    _ = (1 + |2 * Real.pi * t|) /
          Real.log R := by
      rw [div_eq_mul_inv]
      ring
