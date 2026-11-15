-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_divisorMultiplicativePhase_eq_cpow
-- name    : Wikipedia.SzemeredisTheorem.divisorMultiplicativePhase_eq_cpow
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:53:14.838572+00:00
-- url     : https://prove2.me/theorems/2248d18e-b03c-4810-ad34-7e09cce03c34
-- title:
--   The logarithmic divisor phase is a complex power
-- statement:
--   For natural $R>1$ and $d>0$ and a real Fourier parameter $t$, the divisor phase equals
--
--   $$
--   \exp\!\left(-\frac{\log d}{\log R}
--   +2\pi it\frac{\log d}{\log R}\right)
--   =d^{-z_R(t)},\qquad z_R(t)=\frac{1-2\pi it}{\log R}.
--   $$
--
--   The power on the right is the complex power at the positive natural base.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L153-L173

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

theorem Wikipedia.SzemeredisTheorem.divisorMultiplicativePhase_eq_cpow
    {R d : ℕ} (hR : 1 < R) (hd : 0 < d)
    (t : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R d t =
      (d : ℂ) ^ (-cutoffZetaShift R t) := by sorry
