-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:08:28.884355+00:00
-- url     : https://prove2.me/theorems/d735af49-cfee-49da-a768-5ce0c9e9d4ad
-- title:
--   Standard representatives of affine congruence values
-- statement:
--   Let $I$ be a finite variable type, let $D>0$ be a natural modulus, and let $\psi$ be an integer affine form. For a residue vector $x:I\to\mathbb Z/D\mathbb Z$, define the natural residue value to be the standard representative of the reduced affine evaluation:
--
--   $$
--   \operatorname{resval}_D(\psi,x)=\operatorname{val}(\psi(x)\bmod D).
--   $$
--
--   This value lies between zero and $D-1$. The construction connects the affine-congruence model used in local densities with natural-valued divisibility conditions in the carry-block expansion.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCarryBlockEulerBridge.lean#L44-L49

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
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
# Carry-block Euler products for selected CFZ families

The cyclic CFZ lift is not globally periodic modulo a paired divisor LCM:
crossing a representative boundary changes an integer carry.  The preceding
carry-block boundary file replaces that false periodicity by a sound
piecewise-affine model.  This file identifies the exact arithmetic model on
each complete quotient block.

For `D = pairedDivisorLcm z`, a complete block has the form

`x = r + D a`,  with `0 ≤ r_v < D`.

The carry is frozen at the lower corner `D a`.  Thus the block is governed
by the family

`q ↦ cfzCarryAdjustedAffineForm N W b q (cfzCarry q (D a))`.

Its mean over `r` is an exact squarefree CRT Euler product.  Averaging those
products over all complete blocks gives the global blockwise Euler model.
The only losses in comparing it with the original cyclic density are:

* the explicit carry-transition density from `CFZCarryBlockBoundary`;
* the outer partial-block boundary of size
  `O(D * card(CFZVariable k) / N)`.

The affine constants may depend arbitrarily on the block and on the form.
At primes dividing `W` they are still congruent to the reduced residue `b`,
so every supported local density is zero.  At good primes outside `W`,
one-form and rank-two geometry depends only on the coefficients, giving the
usual exact cardinality-at-most-two formula and the uniform `p⁻²` bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic natural representative for an affine residue -/

/-- The standard natural representative of an integer affine form evaluated
on a residue vector. -/
def affineFormResidueValue
    {ι : Type*} [Fintype ι] {D : ℕ} [NeZero D]
    (ψ : AffineForm ι ℤ) (x : ι → ZMod D) : ℕ :=
  (ψ.evalZMod D x).val







/-! ## Complete quotient blocks and their affine families -/









/-! ## Good complete quotient blocks -/













/-! ## Exact blockwise CRT and averaged Euler products -/







/-! ## The complete-block mean is the averaged Euler product -/



/-! ## The outer partial-block boundary -/







/-! ## Unconditional cyclic-to-Euler approximation -/









/-! ## Selected-family specialization -/









/-! ## Carry-dependent constants and primes dividing `W` -/



















/-! ## Good primes outside `W` -/



















end Wikipedia.SzemeredisTheorem


