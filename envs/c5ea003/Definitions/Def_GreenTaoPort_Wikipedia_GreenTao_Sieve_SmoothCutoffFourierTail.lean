-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:30.75386+00:00
-- url     : https://prove2.me/theorems/1554d2f5-17d8-459c-adb5-f0deb9fb41b1
-- title:
--   Absolute Fourier moment densities of smooth sieve cutoffs
-- statement:
--   For a smooth sieve cutoff $\chi$, a natural moment order $k$, and a real frequency $t$, define
--
--   $$
--   m_{\chi,k}(t)=|t|^k\,|\widehat\chi(t)|,
--   $$
--
--   where $\widehat\chi$ denotes the cutoff Fourier transform $\mathcal F(x\mapsto e^x\chi(x))$ fixed by the sieve construction. This nonnegative real density is the integrand for the absolute Fourier moment of order $k$. Subsequent estimates use its integrability and control its integral outside growing symmetric frequency intervals.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothCutoffFourierTail.lean#L25-L28

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Fourier tails for the smooth sieve cutoff

The Fourier transform used by the smooth Goldston--Yıldırım weight is a
Schwartz function.  This file packages the consequence needed by the
multivariate truncation argument: every polynomially weighted absolute
Fourier moment is integrable, and its mass outside the symmetric interval
`[-T, T]` tends to zero.

The last statements specialize the radius to the conventional growing box
`T = sqrt (log R)`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped Topology

namespace SmoothSieveCutoff

/-- The nonnegative density of the `k`-th absolute Fourier moment. -/
noncomputable def fourierMomentDensity
    (χ : SmoothSieveCutoff) (k : ℕ) (t : ℝ) : ℝ :=
  ‖t‖ ^ k * ‖χ.cutoffFourierTransform t‖

















end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


