-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_cutoffZetaShift_le_of_abs_le
-- name    : Wikipedia.SzemeredisTheorem.norm_cutoffZetaShift_le_of_abs_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:09.530192+00:00
-- url     : https://prove2.me/theorems/9653f76d-a03a-43c8-b60e-6336c56dff81
-- title:
--   A uniform zeta-shift bound on a frequency interval
-- statement:
--   Let $R>1$ be an integer and let $t,T\in\mathbb R$ satisfy $|t|\le T$. The cutoff zeta shift obeys
--   $$
--   \|s_R(t)\|\le\frac{1+2\pi T}{\log R}.
--   $$
--   This estimate is uniform over all frequencies in the indicated interval; nonnegativity of $T$ follows from the hypothesis.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L124-L151

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

theorem Wikipedia.SzemeredisTheorem.norm_cutoffZetaShift_le_of_abs_le
    {R : ℕ} (hR : 1 < R)
    {T t : ℝ} (ht : |t| ≤ T) :
    ‖cutoffZetaShift R t‖ ≤
      (1 + 2 * Real.pi * T) /
        Real.log R := by sorry
