-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.divisorMultiplicativePhase_eq_cpow
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:38.368318+00:00
-- url     : https://prove2.me/submissions/95d6d252-cce1-4f14-99b6-cfed9179ed0e

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
/-- The divisor phase is exactly a negative complex power with the shift
above. -/
theorem solution
    {R d : ℕ} (hR : 1 < R) (hd : 0 < d)
    (t : ℝ) :
    SmoothSieveCutoff.divisorMultiplicativePhase R d t =
      (d : ℂ) ^ (-cutoffZetaShift R t) := by
  have hd0 : (d : ℂ) ≠ 0 := by
    exact_mod_cast hd.ne'
  have hlog :
      Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  rw [SmoothSieveCutoff.divisorMultiplicativePhase,
    SmoothSieveCutoff.cutoffMultiplicativePhase,
    Complex.cpow_def_of_ne_zero hd0,
    ← Complex.natCast_log]
  congr 1
  rw [cutoffZetaShift]
  push_cast
  field_simp [hlog]
  ring
