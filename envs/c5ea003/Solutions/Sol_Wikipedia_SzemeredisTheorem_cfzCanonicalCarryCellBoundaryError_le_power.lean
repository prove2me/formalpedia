-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCellBoundaryError_le_power
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:41:56.287917+00:00
-- url     : https://prove2.me/submissions/278aa9f0-792d-45f5-a992-dbc6e3e538c5

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedGoodPrime
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedLocalFactors
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_card_cfzTrimmedFamilyCarryBadPoints_le_power
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cast_pow_sub_trimToMultiple_pow_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_div_trimToMultiple_pow_le_mul_two_pow_div

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm











@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl









end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Explicit power bound for the complete canonical carry-cell error. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D) (hfit : 2 * D ≤ N)
    (forms : κ → CFZFormIndex k) :
    cfzCanonicalCarryCellBoundaryError
        (N := N) D forms ≤
      4 * (D : ℝ) *
          (Fintype.card (CFZVariable k) : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) +
        2 *
          ((cfzCanonicalCarryBoundaryConstant κ k : ℕ) : ℝ) *
          (D : ℝ) *
          (N : ℝ) ^
            (Fintype.card (CFZVariable k) - 1) *
          (2 : ℝ) ^ Fintype.card (CFZVariable k) /
          (N : ℝ) ^ Fintype.card (CFZVariable k) := by
  let t := Fintype.card (CFZVariable k)
  let C := cfzCanonicalCarryBoundaryConstant κ k
  have houter :
      (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
        (D : ℝ) * (t : ℝ) *
          (N : ℝ) ^ (t - 1) :=
    cast_pow_sub_trimToMultiple_pow_le hD
  have hbadNat :
      (cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card ≤
        C * D * N ^ (t - 1) := by
    simpa only [C, t] using
      card_cfzTrimmedFamilyCarryBadPoints_le_power
        hk hD forms
  have hbad :
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) ≤
        (C : ℝ) * (D : ℝ) *
          (N : ℝ) ^ (t - 1) := by
    exact_mod_cast hbadNat
  have hbadDiv :
      ((cfzTrimmedFamilyCarryBadPoints
          (N := N) D forms).card : ℝ) /
          (trimToMultiple D N : ℝ) ^ t ≤
        ((C : ℝ) * (D : ℝ) *
            (N : ℝ) ^ (t - 1)) *
          (2 : ℝ) ^ t / (N : ℝ) ^ t := by
    exact
      div_trimToMultiple_pow_le_mul_two_pow_div
        hD hfit (by positivity) hbad
  unfold cfzCanonicalCarryCellBoundaryError
  simp only [Finset.prod_const, Finset.card_univ]
  change
    4 * (((N ^ t - (trimToMultiple D N) ^ t : ℕ) : ℝ)) /
          (N : ℝ) ^ t +
        2 *
          (((cfzTrimmedFamilyCarryBadPoints
              (N := N) D forms).card : ℝ) /
            (trimToMultiple D N : ℝ) ^ t) ≤
      4 * (D : ℝ) * (t : ℝ) *
          (N : ℝ) ^ (t - 1) / (N : ℝ) ^ t +
        2 * (C : ℝ) * (D : ℝ) *
          (N : ℝ) ^ (t - 1) *
          (2 : ℝ) ^ t / (N : ℝ) ^ t
  apply add_le_add
  · exact
      div_le_div_of_nonneg_right
        (by
          calc
            4 * (((N ^ t -
                (trimToMultiple D N) ^ t : ℕ) : ℝ)) ≤
                4 * ((D : ℝ) * (t : ℝ) *
                  (N : ℝ) ^ (t - 1)) :=
              mul_le_mul_of_nonneg_left houter (by norm_num)
            _ = 4 * (D : ℝ) * (t : ℝ) *
                (N : ℝ) ^ (t - 1) := by ring)
        (by positivity)
  · calc
      2 *
          (((cfzTrimmedFamilyCarryBadPoints
              (N := N) D forms).card : ℝ) /
            (trimToMultiple D N : ℝ) ^ t) ≤
          2 * (((C : ℝ) * (D : ℝ) *
              (N : ℝ) ^ (t - 1)) *
            (2 : ℝ) ^ t / (N : ℝ) ^ t) :=
        mul_le_mul_of_nonneg_left hbadDiv (by norm_num)
      _ = 2 * (C : ℝ) * (D : ℝ) *
          (N : ℝ) ^ (t - 1) *
          (2 : ℝ) ^ t / (N : ℝ) ^ t := by ring
