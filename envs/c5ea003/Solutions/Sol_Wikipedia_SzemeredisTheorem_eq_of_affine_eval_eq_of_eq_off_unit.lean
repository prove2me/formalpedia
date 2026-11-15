-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.eq_of_affine_eval_eq_of_eq_off_unit
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:50:16.183404+00:00
-- url     : https://prove2.me/submissions/fc551ce5-93a0-4bcd-a98e-f5ebcaf7cc02

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
/-! ## A generic unit-coefficient strip count -/

open Wikipedia.SzemeredisTheorem in
/-- If an affine form has coefficient `1` or `-1` in coordinate `v`, its
value together with all other coordinates determines the point. -/
theorem solution
    {ι : Type*} [Fintype ι]
    (ψ : AffineForm ι ℤ) (v : ι)
    (hunit :
      ψ.coefficient v = 1 ∨ ψ.coefficient v = -1)
    {x y : ι → ℕ}
    (heval :
      ψ.eval (fun i => (x i : ℤ)) =
        ψ.eval (fun i => (y i : ℤ)))
    (hoff : ∀ i, i ≠ v → x i = y i) :
    x = y := by
  classical
  funext i
  by_cases hiv : i = v
  · subst i
    simp only [AffineForm.eval] at heval
    have hoffsum :
        ∑ j ∈ (Finset.univ.erase v),
            ψ.coefficient j * (x j : ℤ) =
          ∑ j ∈ (Finset.univ.erase v),
            ψ.coefficient j * (y j : ℤ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hoff j (Finset.ne_of_mem_erase hj)]
    have hxsum :
        ∑ j, ψ.coefficient j * (x j : ℤ) =
          (∑ j ∈ (Finset.univ.erase v),
              ψ.coefficient j * (x j : ℤ)) +
            ψ.coefficient v * (x v : ℤ) := by
      symm
      exact Finset.sum_erase_add _ _
        (Finset.mem_univ v)
    have hysum :
        ∑ j, ψ.coefficient j * (y j : ℤ) =
          (∑ j ∈ (Finset.univ.erase v),
              ψ.coefficient j * (y j : ℤ)) +
            ψ.coefficient v * (y v : ℤ) := by
      symm
      exact Finset.sum_erase_add _ _
        (Finset.mem_univ v)
    rw [hxsum, hysum, hoffsum] at heval
    rcases hunit with hunit | hunit
    · rw [hunit] at heval
      norm_num at heval
      exact_mod_cast heval
    · rw [hunit] at heval
      norm_num at heval
      exact_mod_cast heval
  · exact hoff i hiv
