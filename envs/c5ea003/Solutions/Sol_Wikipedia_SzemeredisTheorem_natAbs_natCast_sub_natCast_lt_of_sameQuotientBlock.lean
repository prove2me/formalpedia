-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.natAbs_natCast_sub_natCast_lt_of_sameQuotientBlock
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:16:29.191481+00:00
-- url     : https://prove2.me/submissions/204e7c27-a44e-49e4-89a6-03a4cb966706

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
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
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Carry-block boundaries for the cyclic CFZ lift

The standard representative of a CFZ form modulo `N` is not periodic in the
natural input coordinates.  This file gives the unconditional replacement
for the false periodicity step.

We divide the standard box into coordinatewise quotient blocks of side `D`.
On a block where every selected CFZ carry is constant, the cyclic lift is an
ordinary affine form with a carry-dependent constant.  A block on which one
carry changes must cross a hyperplane at an integral multiple of `N`.
Because CFZ coefficients are bounded and every CFZ form has a coefficient
equal to `1` or `-1`, the union of all such blocks has an explicit
codimension-one cardinality bound.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Coordinate quotient blocks -/

open Wikipedia.SzemeredisTheorem in
/-- Coordinates in the same positive-side quotient block differ by less
than the block side. -/
theorem solution
    {ι : Type*} {D : ℕ} (hD : 0 < D)
    {x y : ι → ℕ} (hxy : SameQuotientBlock D x y)
    (i : ι) :
    Int.natAbs ((x i : ℤ) - (y i : ℤ)) < D := by
  have hdecomp :
      (x i : ℤ) - (y i : ℤ) =
        ((x i % D : ℕ) : ℤ) - ((y i % D : ℕ) : ℤ) := by
    have hx :
        x i = x i % D + D * (x i / D) := by
      exact (Nat.mod_add_div (x i) D).symm
    have hy :
        y i = y i % D + D * (y i / D) := by
      exact (Nat.mod_add_div (y i) D).symm
    have hxZ :
        (x i : ℤ) =
          ((x i % D : ℕ) : ℤ) +
            (D : ℤ) * ((x i / D : ℕ) : ℤ) := by
      exact_mod_cast hx
    have hyZ :
        (y i : ℤ) =
          ((y i % D : ℕ) : ℤ) +
            (D : ℤ) * ((y i / D : ℕ) : ℤ) := by
      exact_mod_cast hy
    rw [hxZ, hyZ, hxy i]
    ring
  rw [hdecomp]
  exact Int.natAbs_coe_sub_coe_lt_of_lt
    (Nat.mod_lt _ hD) (Nat.mod_lt _ hD)
