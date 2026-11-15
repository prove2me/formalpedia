-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cast_pow_sub_trimToMultiple_pow_le
-- name    : Wikipedia.SzemeredisTheorem.cast_pow_sub_trimToMultiple_pow_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:48:44.709394+00:00
-- url     : https://prove2.me/theorems/c2c0be2d-d761-4a34-9e08-063e0f92debc
-- title:
--   A power bound for trimming a side length to a multiple
-- statement:
--   Let $D>0$ and $N,t\in\mathbb N$, and put $T=D\lfloor N/D\rfloor$. Then
--
--   $$
--   N^t-T^t\le Dt\,N^{t-1},
--   $$
--
--   with the difference interpreted as natural subtraction and the exponent $t-1$ truncated at zero. The statement includes $t=0$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCongruenceBoundary.lean#L982-L1025

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Finite-box congruence boundaries for the CFZ divisor expansion

This file isolates the exact finite-box step between the divisor expansion
and the prime-local arithmetic.  It has three layers.

* A normalized boundary estimate compares a bounded periodic function on a
  natural box with its exact residue-class mean.
* Coordinatewise `Fin`/`ZMod` equivalences identify the mean on a
  `CubePoint k N` with the corresponding natural box mean.
* For the cyclic representative used by `cfzWTrickedLinearValue`, periodicity
  modulo a divisor modulus `D` is proved under the precise compatibility
  hypothesis `D ∣ W * N`.

The compatibility hypothesis in the last item is mathematically necessary
for this direct rectangular trimming argument: reducing a form modulo `N`
can change an integer lift by a multiple of `N`, and the subsequent
`W`-trick changes its value by a multiple of `W * N`.  Without divisibility
by `D`, an unconditional treatment must subdivide the box into carry cells
on which every modular reduction has a fixed integer lift.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Why cyclic representatives need a compatibility or carry argument -/
/-! ## Weighted lifts through two moduli -/
/-! ## Natural representatives of CFZ cube points -/
/-! ## Canonical carry cells -/
/-! ## Divisibility indicators modulo a common multiple -/
/-! ## Exact finite-box and residue-vector reindexing -/
/-! ## Reindexing the cyclic CFZ cube -/
/-! ## CFZ periodicity under lift compatibility -/
/-! ## The exact affine residue model -/
/-! ## Normalized trimming loss -/
/-! ## Paired divisibility specialization -/

theorem Wikipedia.SzemeredisTheorem.cast_pow_sub_trimToMultiple_pow_le
    {D N t : ℕ} (hD : 0 < D) :
    (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
      (D : ℝ) * (t : ℝ) * (N : ℝ) ^ (t - 1) := by sorry
