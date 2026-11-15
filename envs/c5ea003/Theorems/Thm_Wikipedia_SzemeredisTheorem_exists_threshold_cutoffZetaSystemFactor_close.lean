-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_threshold_cutoffZetaSystemFactor_close
-- name    : Wikipedia.SzemeredisTheorem.exists_threshold_cutoffZetaSystemFactor_close
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:03:12.992738+00:00
-- url     : https://prove2.me/theorems/3bcfebb1-2904-4122-830e-47f450d1156a
-- title:
--   Uniform zeta-factor control on square-root logarithmic boxes
-- statement:
--   For any finite index type $\kappa$ and $\varepsilon>0$, there is a natural threshold $R_0$ such that for every $R\ge R_0$ and all real coordinate vectors satisfying $|t_i|,|u_i|\le\sqrt{\log R}$, the cutoff zeta-system factor differs from $1$ in norm by less than $\varepsilon$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L339-L400

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

theorem Wikipedia.SzemeredisTheorem.exists_threshold_cutoffZetaSystemFactor_close
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ,
      ∀ R, R₀ ≤ R →
      ∀ (t u : κ → ℝ),
        (∀ i, |t i| ≤ Real.sqrt (Real.log R)) →
        (∀ i, |u i| ≤ Real.sqrt (Real.log R)) →
        ‖cutoffZetaSystemFactor R t u - 1‖ < ε := by sorry
