-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cutoffZetaShift_add_ne_zero
-- name    : Wikipedia.SzemeredisTheorem.cutoffZetaShift_add_ne_zero
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:36.330015+00:00
-- url     : https://prove2.me/theorems/a0a750fa-f6ca-4a73-86dd-53ce8c251275
-- title:
--   Pairwise sums of cutoff zeta shifts are nonzero
-- statement:
--   Let $R>1$ be a natural number and let $t,u\in\mathbb R$. Denote the cutoff zeta shift at scale $R$ and frequency $v$ by $s_R(v)$. Then
--   $$
--   s_R(t)+s_R(u)\ne0.
--   $$
--   The statement holds for every pair of real frequencies and requires no restriction on their signs or magnitudes.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L67-L81

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

theorem Wikipedia.SzemeredisTheorem.cutoffZetaShift_add_ne_zero
    {R : ℕ} (hR : 1 < R) (t u : ℝ) :
    cutoffZetaShift R t +
        cutoffZetaShift R u ≠ 0 := by sorry
