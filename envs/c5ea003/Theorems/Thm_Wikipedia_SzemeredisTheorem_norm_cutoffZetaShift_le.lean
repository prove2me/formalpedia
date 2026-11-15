-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_cutoffZetaShift_le
-- name    : Wikipedia.SzemeredisTheorem.norm_cutoffZetaShift_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:18:09.476858+00:00
-- url     : https://prove2.me/theorems/6abd9896-8f19-4c60-befe-512f615ecaa4
-- title:
--   An elementary bound for the Fourier zeta shift
-- statement:
--   Let $R>1$ be an integer and let $t\in\mathbb R$. The cutoff zeta shift $s_R(t)$ satisfies
--   $$
--   \|s_R(t)\|\le\frac{1+|2\pi t|}{\log R}.
--   $$
--   The logarithm is positive under the stated scale assumption, and no truncation restriction is imposed on the frequency.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L83-L122

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

theorem Wikipedia.SzemeredisTheorem.norm_cutoffZetaShift_le
    {R : ℕ} (hR : 1 < R) (t : ℝ) :
    ‖cutoffZetaShift R t‖ ≤
      (1 + |2 * Real.pi * t|) /
        Real.log R := by sorry
