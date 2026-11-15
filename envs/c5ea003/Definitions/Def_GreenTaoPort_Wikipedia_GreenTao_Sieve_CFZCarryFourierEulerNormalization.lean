-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:15:02.507912+00:00
-- url     : https://prove2.me/theorems/3dcd9337-53b4-4cf3-a273-894e3386fcb6
-- title:
--   Residual factors after Selberg and singular-zeta normalization
-- statement:
--   For a finite index set, natural parameters $R,w$, real Fourier families $t,u$, and a complex large-prime correction $L$, the normalized completed correction is the product of three factors:
--
--   $$
--   \operatorname{SmallPrimeCorrection}(R,w,t,u)\,
--   \operatorname{CompletedZetaFactor}(R,t,u)\,L.
--   $$
--
--   The first factor records the normalized small-prime zeta correction, the second uses the completed cutoff zeta-system factor, and the supplied factor $L$ carries the remaining large-prime correction. This definition records the exact residual product after the explicit Selberg and singular-zeta normalizations; it imposes no analytic bounds on its parameters.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryFourierEulerNormalization.lean#L26-L33

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
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
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
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
# Normalized completed Euler model on CFZ carry blocks

This file assembles three pieces that were previously separate:

* the exact Selberg/Fourier/singular-zeta normalization;
* the exact small-prime/large-prime factorization for a carry block;
* the uniform limits of the normalized small-prime correction, completed
  zeta factor, and large-prime correction.

The resulting pointwise identity is the normalized form of the *completed
Euler model*.  It deliberately does not identify that model with the
finite `d ≤ R` divisor sum; the honest truncation-to-Euler splice remains a
separate analytic theorem.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-- The product of the three residual factors left after exact Selberg and
singular-zeta normalization. -/
noncomputable def normalizedCompletedFourierEulerCorrection
    {κ : Type*} [Fintype κ]
    (R w : ℕ) (t u : κ → ℝ) (largeCorrection : ℂ) : ℂ :=
  normalizedSmallPrimeZetaCorrection R w t u *
    cutoffZetaSystemFactor R t u *
    largeCorrection



/-! ## Uniform convergence of the residual factors -/





end Wikipedia.SzemeredisTheorem


