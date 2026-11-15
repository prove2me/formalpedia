-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_cfzCoefficient_eq_one_or_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:51:26.791207+00:00
-- url     : https://prove2.me/submissions/869e88b9-3b98-40d7-997b-8b927769cde8

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

section


/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/

namespace Wikipedia.SzemeredisTheorem











@[simp]
theorem cfzCoefficient_selected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) =
      (i.1 : ℤ) - (q.1 : ℤ) := by
  simp [cfzCoefficient, i.2]

















end Wikipedia.SzemeredisTheorem

end
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
/-! ## A generic unit-coefficient strip count -/
/-! ## CFZ coefficient and block-diameter facts -/

open Wikipedia.SzemeredisTheorem in
/-- Every CFZ form has a doubled coordinate with coefficient exactly `1` or
`-1`.  The adjacent undeleted coordinate supplies it. -/
theorem solution
    {k : ℕ} (hk : 2 ≤ k) (q : CFZFormIndex k) :
    ∃ v : CFZVariable k,
      cfzCoefficient q v = 1 ∨
        cfzCoefficient q v = -1 := by
  rcases q with ⟨j, ω⟩
  by_cases hj : (j : ℕ) = 0
  · let i : Fin k := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      simp [i, hj] at hval
    let i' : {i : Fin k // i ≠ j} := ⟨i, hij⟩
    refine ⟨(i, ω i'), Or.inl ?_⟩
    rw [cfzCoefficient_selected ⟨j, ω⟩ i']
    change ((1 : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 1
    rw [hj]
    norm_num
  · have hjpos : 0 < (j : ℕ) := Nat.pos_of_ne_zero hj
    let i : Fin k := ⟨(j : ℕ) - 1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hval := congrArg Fin.val h
      simp [i] at hval
      omega
    let i' : {i : Fin k // i ≠ j} := ⟨i, hij⟩
    refine ⟨(i, ω i'), Or.inr ?_⟩
    rw [cfzCoefficient_selected ⟨j, ω⟩ i']
    change
      (((j : ℕ) - 1 : ℕ) : ℤ) -
          ((j : ℕ) : ℤ) = -1
    rw [Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr hj)]
    norm_num
