-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cfzCanonicalCarryCellBoundaryError_le_div
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:43:16.131267+00:00
-- url     : https://prove2.me/submissions/497e01e6-96b1-4321-ab0e-399855d76934

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cfzCanonicalCarryCellBoundaryError_le_power

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
/-- Collapsed `C_{k,|κ|} D/N` form of the complete canonical carry-cell
boundary error. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N D : ℕ} [NeZero N]
    (hk : 2 ≤ k) (hD : 0 < D) (hfit : 2 * D ≤ N)
    (forms : κ → CFZFormIndex k) :
    cfzCanonicalCarryCellBoundaryError
        (N := N) D forms ≤
      (cfzCanonicalCarryCellErrorConstant κ k : ℝ) *
        (D : ℝ) / (N : ℝ) := by
  have hbase :=
    cfzCanonicalCarryCellBoundaryError_le_power
      hk hD hfit forms
  let t := Fintype.card (CFZVariable k)
  have hkpos : 0 < k := by omega
  have htpos : 0 < t := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(⟨0, hkpos⟩, false)⟩
  have htOne : 1 ≤ t := htpos
  have hpow :
      (N : ℝ) ^ t =
        (N : ℝ) ^ (t - 1) * (N : ℝ) := by
    calc
      (N : ℝ) ^ t =
          (N : ℝ) ^ ((t - 1) + 1) := by
        rw [Nat.sub_add_cancel htOne]
      _ = (N : ℝ) ^ (t - 1) * (N : ℝ) := by
        rw [pow_succ]
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast NeZero.ne N
  calc
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
          (N : ℝ) ^ Fintype.card (CFZVariable k) :=
      hbase
    _ =
      (cfzCanonicalCarryCellErrorConstant κ k : ℝ) *
        (D : ℝ) / (N : ℝ) := by
      change
        4 * (D : ℝ) * (t : ℝ) *
              (N : ℝ) ^ (t - 1) / (N : ℝ) ^ t +
            2 *
              (cfzCanonicalCarryBoundaryConstant κ k : ℝ) *
              (D : ℝ) * (N : ℝ) ^ (t - 1) *
              (2 : ℝ) ^ t / (N : ℝ) ^ t =
          (cfzCanonicalCarryCellErrorConstant κ k : ℝ) *
            (D : ℝ) / (N : ℝ)
      rw [hpow]
      unfold cfzCanonicalCarryCellErrorConstant
      push_cast
      field_simp
      ring
