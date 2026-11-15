-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:12:52.669193+00:00
-- url     : https://prove2.me/theorems/7ba1a0b2-6dba-4a8e-8661-b329fa8c26ae
-- title:
--   A common carry-Euler error constant for each progression length
-- statement:
--   For a natural progression length $k$, the selected CFZ carry-Euler error constant is the existing complex arithmetic-to-zeta ratio error constant evaluated at the cardinality of the full CFZ form index type. This fixes one real constant from the ambient progression length before choosing a Boolean subfamily or a carry block. Its uniformity is used later to bound the Euler errors for every selected family at that length.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryEulerTail.lean#L224-L229

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Uniform Euler tails on CFZ carry blocks

The carry-block reduction leaves a genuinely varying affine system.  The
paired divisor choice determines the block side length, the point of the
quotient block determines all carry constants, and all of these data may
vary with the asymptotic parameter.  This file keeps that dependence.

At a prime outside the primorial, carry corrections alter only affine
constants.  The direct modular one-form and rank-two predicates therefore
give the same `O_k(p⁻²)` arithmetic-to-zeta ratio estimate on every block,
uniformly in the divisor choice and in both Fourier variables.  The general
dominated Euler-product theorem then shows that the product over `p > w`
tends to one as `w → ∞`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## A dependent package for a varying carry block -/



namespace SelectedCFZCarryFourierBlockData







end SelectedCFZCarryFourierBlockData

/-! ## Direct modular local estimate -/





/-! ## A `k`-only bound for every selected block -/

/-- One error constant for all selected carry blocks at ambient
progression length `k`. -/
noncomputable def selectedCFZCarryEulerTailErrorConstant
    (k : ℕ) : ℝ :=
  complexArithmeticZetaRatioErrorConstant
    (Fintype.card (CFZFormIndex k))









/-! ## Uniform large-prime tail -/



end Wikipedia.SzemeredisTheorem


