-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:12:58.840138+00:00
-- url     : https://prove2.me/theorems/62e29a8b-fda3-47b6-8d6c-85f851857467
-- title:
--   Explicit combinatorial constants for canonical carry boundaries
-- statement:
--   Let $K$ be a finite selected-form index type, let $V$ be the doubled CFZ variable type at progression length $k$, and let $C_k$ be the fixed carry-range bound. The carry-transition constant is
--
--   $$
--   B=|K|(2C_k+1)(2|V|k+1).
--   $$
--
--   The full cell-error coefficient is $4|V|+2B\,2^{|V|}$. These natural constants collect the outer trimming loss and all carry-transition cells into one uniform boundary estimate. They depend on the ambient length and finite index cardinalities, rather than the cyclic modulus or particular divisor choices.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalCarryBoundaryBound.lean#L22-L223

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
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
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Power bounds for the canonical carry-cell boundary

The canonical carry Euler bridge has an exact error with two terms:

* the outer part of the `N`-box removed when trimming to side-`D` blocks;
* the carry-transition set inside the trimmed box.

This file converts that exact expression into the standard power estimate.
Under `2 * D ≤ N`, the trimmed side is at least `N / 2`; hence its
`t`-dimensional volume loses at most a factor `2^t`.  Combining this with
the existing codimension-one carry-transition count gives an explicit
`O_{k,|κ|}(D/N)` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Combinatorial constant in the family carry-transition count. -/
def cfzCanonicalCarryBoundaryConstant
    (κ : Type*) [Fintype κ] (k : ℕ) : ℕ :=
  Fintype.card κ *
    ((2 * cfzCarryRange k + 1) *
      (2 * Fintype.card (CFZVariable k) * k + 1))











/-- A single explicit coefficient for the outer trimming loss and all
canonical carry-transition cells. -/
def cfzCanonicalCarryCellErrorConstant
    (κ : Type*) [Fintype κ] (k : ℕ) : ℕ :=
  4 * Fintype.card (CFZVariable k) +
    2 * cfzCanonicalCarryBoundaryConstant κ k *
      2 ^ Fintype.card (CFZVariable k)



end Wikipedia.SzemeredisTheorem


