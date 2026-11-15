-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_fourierZetaBoxRadius_real
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:54.8717+00:00
-- url     : https://prove2.me/submissions/d8cc0829-3a18-49d4-8ea8-0a1f38888796

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
/-! ## Finite Fourier systems -/
/-! ## The standard growing truncation box -/

open Wikipedia.SzemeredisTheorem in
/-- The scalar radius controlling the box `|t| ≤ sqrt (log R)` tends to
zero. -/
theorem solution :
    Tendsto
      (fun x : ℝ =>
        (1 + 2 * Real.pi * Real.sqrt x) / x)
      atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun x : ℝ => x⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hsqrtInv :
      Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹)
        atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      Real.tendsto_sqrt_atTop
  have hsum :
      Tendsto
        (fun x : ℝ =>
          x⁻¹ +
            (2 * Real.pi) *
              (Real.sqrt x)⁻¹)
        atTop (𝓝 0) := by
    simpa using hinv.add
      ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ => 2 * Real.pi)
            atTop (𝓝 (2 * Real.pi))).mul
        hsqrtInv)
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hsqrt :
      0 < Real.sqrt x :=
    Real.sqrt_pos.2 hx
  have hsquare :
      (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt hx.le
  have hsqrtDiv :
      Real.sqrt x / x =
        (Real.sqrt x)⁻¹ := by
    calc
      Real.sqrt x / x =
          Real.sqrt x / (Real.sqrt x) ^ 2 := by
        rw [hsquare]
      _ = (Real.sqrt x)⁻¹ := by
        field_simp [hsqrt.ne']
  rw [add_div, one_div, mul_div_assoc, hsqrtDiv]
