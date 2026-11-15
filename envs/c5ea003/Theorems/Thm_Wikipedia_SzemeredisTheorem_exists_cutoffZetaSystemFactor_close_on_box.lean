-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cutoffZetaSystemFactor_close_on_box
-- name    : Wikipedia.SzemeredisTheorem.exists_cutoffZetaSystemFactor_close_on_box
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:55:39.82186+00:00
-- url     : https://prove2.me/theorems/203aa537-dd76-4ccf-a4f2-0c35336afa1d
-- title:
--   A scalar radius gives uniform zeta-factor control on a Fourier box
-- statement:
--   For any finite index type $\kappa$ and $\varepsilon>0$, there is $\delta>0$ such that whenever $R>1$, $t,u:\kappa\to\mathbb R$ satisfy $|t_i|,|u_i|\le T$, and $(1+2\pi T)/\log R<\delta$, the cutoff zeta-system factor differs from $1$ in norm by less than $\varepsilon$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L253-L277

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

theorem Wikipedia.SzemeredisTheorem.exists_cutoffZetaSystemFactor_close_on_box
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ {R : ℕ}, 1 < R →
      ∀ {T : ℝ} (t u : κ → ℝ),
        (1 + 2 * Real.pi * T) /
            Real.log R < δ →
        (∀ i, |t i| ≤ T) →
        (∀ i, |u i| ≤ T) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by sorry
