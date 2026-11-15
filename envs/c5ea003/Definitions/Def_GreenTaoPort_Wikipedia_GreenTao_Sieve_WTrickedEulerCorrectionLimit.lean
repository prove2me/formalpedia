-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:16.199201+00:00
-- url     : https://prove2.me/theorems/80334ccf-de00-48f3-b841-decdf28f156a
-- title:
--   Normalized phase residuals and their logarithmic size bound
-- statement:
--   For a natural modulus $p$ and a pair of complex phases, the one-pair residual multiplies the inverse phase-pair zeta local model by $1-p^{-1}$. For a finite phase system of size $m$, the system residual analogously uses $(1-p^{-1})^m$ times the inverse system local factor.
--
--   At natural parameters $R,w$ and real Fourier radius $T$, the common phase-magnitude bound is
--
--   $$
--   \frac{\log w}{\log R}(1+2\pi T).
--   $$
--
--   The expressions are total. The positive-level and frequency restrictions needed to interpret this scalar as a bound are assumptions of the subsequent convergence estimates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/WTrickedEulerCorrectionLimit.lean#L63-L524

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Lean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Quantitative convergence of the W-tricked Euler correction

`WTrickedEulerCorrection` writes the normalized finite small-prime
correction as

`∏_{p ≤ w} ((1 - p⁻¹)^m * Z_p(z, v)⁻¹)`.

This file controls that product when every phase is close to one.  The
important cancellation is

`z + v - z v - 1 = -(1-z)(1-v)`,

so the perturbation is quadratic in the phase error.  We first prove a
one-pair bound valid at every prime, then accumulate it over the finite
form system and over all primes at most `w`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## One paired phase -/



/-- The normalized residual for one paired phase. -/
noncomputable def phasePairNormalizationResidual
    (p : ℕ) (z v : ℂ) : ℂ :=
  (1 - (p : ℂ)⁻¹) *
    (phasePairZetaEulerLocalModel p z v)⁻¹









/-! ## A finite system at one prime -/

/-- The normalized residual of a finite phase system at one prime. -/
noncomputable def phaseSystemNormalizationResidual
    {κ : Type*} [Fintype κ]
    (p : ℕ) (z v : κ → ℂ) : ℂ :=
  unshiftedZetaSystemLocalFactor
      (Fintype.card κ) p *
    (phaseZetaSystemEulerLocalFactor p z v)⁻¹





/-! ## Accumulation over the small primes -/









/-! ## The actual cutoff phases -/

/-- Common logarithmic phase-size bound on primes at most `w` and Fourier
parameters of absolute value at most `T`. -/
noncomputable def cutoffPhaseMagnitudeBound
    (R w : ℕ) (T : ℝ) : ℝ :=
  (Real.log w / Real.log R) *
    (1 + 2 * Real.pi * T)









/-! ## Linearized control and joint convergence -/







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cutoffPhaseMagnitudeBound.eq_1,
    `Wikipedia.SzemeredisTheorem.phasePairNormalizationResidual.eq_1,
    `Wikipedia.SzemeredisTheorem.phaseSystemNormalizationResidual.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


