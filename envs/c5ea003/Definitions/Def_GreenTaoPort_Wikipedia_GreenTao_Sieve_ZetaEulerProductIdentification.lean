-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:51:38.289911+00:00
-- url     : https://prove2.me/theorems/f9757b9d-cdf5-48a7-975b-1ea68973fc85
-- title:
--   Paired zeta Euler factors and their singular contribution
-- statement:
--   At a prime $p$ and complex shifts $u,v$, the paired zeta local model is
--
--   $$
--   \frac{(1-p^{-(1+u)})(1-p^{-(1+v)})}
--    {1-p^{-(1+u+v)}}.
--   $$
--
--   The system factor multiplies this expression over a finite index set. The cutoff specialization substitutes the precise Fourier shifts $(1-2\pi it)/\log R$ on each side. The associated singular factor is the product of $uv/(u+v)$ over these paired shifts, recording the elementary pole contribution after completing the zeta factors. Analytic nonvanishing and convergence are supplied separately.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ZetaEulerProductIdentification.lean#L40-L122

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Lean
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
# Identifying the zeta-model Euler product

The model local factor attached to one pair of Fourier shifts `u,v` is

`(1 - p^(-1-u)) (1 - p^(-1-v)) / (1 - p^(-1-u-v))`.

Mathlib's Euler product for `riemannZeta` identifies its prime product with

`ζ(1+u+v) / (ζ(1+u) ζ(1+v))`

whenever the real parts of `u` and `v` are positive.  This file proves that
identity first for one pair and then for an arbitrary finite system.  It
then specializes to the exact Mathlib Fourier shifts and splits the answer
into the elementary singular factor and the removable completed factor from
`ZetaNearOne`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



/-- The per-prime zeta model for one pair of shifts. -/
noncomputable def zetaPairEulerLocalFactor
    (u v : ℂ) (p : Nat.Primes) : ℂ :=
  (1 - (p : ℂ) ^ (-(1 + u))) *
    (1 - (p : ℂ) ^ (-(1 + v))) *
      (1 - (p : ℂ) ^ (-(1 + u + v)))⁻¹



/-- Product of all per-pair zeta-model factors at one prime. -/
noncomputable def zetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (u v : κ → ℂ) (p : Nat.Primes) : ℂ :=
  ∏ i, zetaPairEulerLocalFactor (u i) (v i) p



/-- The zeta model specialized to the exact cutoff Fourier shifts. -/
noncomputable def cutoffZetaEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    (p : Nat.Primes) : ℂ :=
  zetaSystemEulerLocalFactor
    (fun i => cutoffZetaShift R (t i))
    (fun i => cutoffZetaShift R (u i)) p

/-- The elementary pole contribution left after completing every zeta
factor. -/
noncomputable def cutoffZetaSingularFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ i,
    (cutoffZetaShift R (t i) *
        cutoffZetaShift R (u i)) /
      (cutoffZetaShift R (t i) +
        cutoffZetaShift R (u i))





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.cutoffZetaSingularFactor.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


