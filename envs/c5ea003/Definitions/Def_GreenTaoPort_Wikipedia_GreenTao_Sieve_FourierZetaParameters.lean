-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:50.646486+00:00
-- url     : https://prove2.me/theorems/e88b8bb0-bb73-48c8-a051-dc6bb4ee88d6
-- title:
--   Complex shifts associated with the sieve Fourier transform
-- statement:
--   For a natural sieve level $R$ and a real Fourier parameter $t$, define the complex shift
--
--   $$
--   z_R(t)=\frac{1-2\pi i t}{\log R}.
--   $$
--
--   The expression follows the analyst normalization of the Fourier transform and fixes both its sign and the factor $2\pi$. For a finite index set $K$ and real parameter families $t,u:K\to\mathbb R$, the system factor is the residue-normalized zeta-system factor evaluated at $(z_R(t_q),z_R(u_q))_{q\in K}$. The formulas are total using the real inverse convention; later estimates impose $R>1$ so that the real part of each shift is positive.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/FourierZetaParameters.lean#L28-L201

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.LSeries.Dirichlet
import Lean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
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

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-- The exact zeta shift belonging to Mathlib's Fourier parameter `t`. -/
noncomputable def cutoffZetaShift
    (R : ℕ) (t : ℝ) : ℂ :=
  (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
    ((1 : ℂ) -
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)



















/-! ## Finite Fourier systems -/

/-- The completed zeta factor for a finite system of paired Fourier
parameters. -/
noncomputable def cutoffZetaSystemFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ) : ℂ :=
  normalizedZetaSystemFactor
    (fun i => cutoffZetaShift R (t i))
    (fun i => cutoffZetaShift R (u i))







/-! ## The standard growing truncation box -/







end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cutoffZetaShift.eq_1,
    `Wikipedia.SzemeredisTheorem.cutoffZetaSystemFactor.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


