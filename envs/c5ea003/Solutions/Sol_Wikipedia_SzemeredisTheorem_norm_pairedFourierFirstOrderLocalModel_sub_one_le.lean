-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_pairedFourierFirstOrderLocalModel_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:23:50.286952+00:00
-- url     : https://prove2.me/submissions/041e13e9-59f5-4606-9f4b-a495adeacc26

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CyclicMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeAffineRank
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_GoodPrimeLocalFactorBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedDivisibilityCRT
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PairedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_pairedFourierPrimeCoefficient_le_three_mul_rpow

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Unrestricted finite-prime-support Euler series

An Euler product is not the pointwise factorization of the divisor sum in
which every divisor is separately truncated by `d ≤ R`.  This file records
the honest unrestricted object that has such a factorization.

For a prime-indexed family `L p`, put

`E S = ∏ p ∈ S, (L p - 1)`

for a finite set of active primes `S`.  If the local errors are absolutely
summable, then the series over all finite prime supports is absolutely
summable and

`∑' S, E S = ∏' p, L p`.

Thus the unrestricted squarefree prime-support expansion has a rigorous
Euler product, with no divisor cutoff and no conditional rearrangement.
The final section specializes the construction to the exact paired Fourier
local factors.  Comparing this unrestricted series with the original
coordinatewise truncation remains a separate approximation theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Generic absolutely convergent support expansion -/
/-! ## Absolute convergence of paired-Fourier local errors -/

open Wikipedia.SzemeredisTheorem in
/-- The first-order part of a paired Fourier factor is bounded by the
summable prime power `p^(-1-1/log R)`. -/
theorem solution
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 2 ≤ R)
    (p : Nat.Primes) (t u : κ → ℝ) :
    ‖pairedFourierFirstOrderLocalModel
          R (p : ℕ) t u - 1‖ ≤
      (3 * Fintype.card κ : ℝ) *
        (p : ℝ) ^
          (-(Real.log (R : ℝ))⁻¹ - 1) := by
  let x : ℝ :=
    (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹)
  have hp0 : 0 < (p : ℝ) := by
    exact_mod_cast p.prop.pos
  have hsum :
      ‖∑ q : κ,
          pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)‖ ≤
        (Fintype.card κ : ℝ) * (3 * x) := by
    calc
      ‖∑ q : κ,
          pairedFourierPrimeCoefficient
            R (p : ℕ) (t q) (u q)‖ ≤
          ∑ q : κ,
            ‖pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q)‖ :=
        norm_sum_le Finset.univ _
      _ ≤ ∑ _q : κ, 3 * x := by
        apply Finset.sum_le_sum
        intro q _hq
        exact
          norm_pairedFourierPrimeCoefficient_le_three_mul_rpow
            hR p (t q) (u q)
      _ = (Fintype.card κ : ℝ) * (3 * x) := by simp
  have hpower :
      x / (p : ℝ) =
        (p : ℝ) ^
          (-(Real.log (R : ℝ))⁻¹ - 1) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one,
      ← Real.rpow_add hp0]
    simp only [sub_eq_add_neg]
  rw [pairedFourierFirstOrderLocalModel,
    complexFirstOrderLocalModel]
  have hrearrange :
      (1 -
          (∑ q : κ,
            pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q)) /
            ((p : ℕ) : ℂ)) -
          1 =
        -((∑ q : κ,
            pairedFourierPrimeCoefficient
              R (p : ℕ) (t q) (u q)) /
            ((p : ℕ) : ℂ)) := by
    ring
  rw [hrearrange, norm_neg, norm_div,
    Complex.norm_natCast]
  calc
    ‖∑ q : κ,
        pairedFourierPrimeCoefficient
          R (p : ℕ) (t q) (u q)‖ /
        (p : ℝ) ≤
      ((Fintype.card κ : ℝ) * (3 * x)) /
        (p : ℝ) := by
      exact div_le_div_of_nonneg_right hsum hp0.le
    _ =
      (3 * Fintype.card κ : ℝ) *
        (p : ℝ) ^
          (-(Real.log (R : ℝ))⁻¹ - 1) := by
      rw [← hpower]
      ring
