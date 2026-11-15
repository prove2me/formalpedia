-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.card_cfzCarryHyperplaneEnvelope_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:52:32.397663+00:00
-- url     : https://prove2.me/submissions/1b91b8dd-f124-4eef-b541-77d84e1bc171

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_card_affineStripInBox_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_cfzCoefficient_eq_one_or_neg_one

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
/-! ## Carry-change hyperplanes -/
/-! ## Explicit bad-point counts -/

open Wikipedia.SzemeredisTheorem in
/-- Exact cardinality bound for the one-form carry-hyperplane envelope. -/
theorem solution
    {k N D : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    (cfzCarryHyperplaneEnvelope (N := N) D q).card ≤
      (2 * cfzCarryRange k + 1) *
        (2 * cfzBlockVariation k D + 1) *
        N ^ (Fintype.card (CFZVariable k) - 1) := by
  classical
  obtain ⟨v, hv⟩ :=
    exists_cfzCoefficient_eq_one_or_neg_one hk q
  have hunit :
      (cfzAffineForm q).coefficient v = 1 ∨
        (cfzAffineForm q).coefficient v = -1 := by
    simpa only [cfzAffineForm_coefficient] using hv
  have hstrip :
      ∀ c : ℤ,
        (affineStripInBox N (cfzBlockVariation k D)
            (cfzAffineForm q) ((N : ℤ) * c)).card ≤
          (2 * cfzBlockVariation k D + 1) *
            N ^ (Fintype.card (CFZVariable k) - 1) :=
    fun c =>
      card_affineStripInBox_le
        N (cfzBlockVariation k D) (cfzAffineForm q)
        ((N : ℤ) * c) v hunit
  calc
    (cfzCarryHyperplaneEnvelope (N := N) D q).card ≤
        ∑ c ∈ Finset.Icc (-(cfzCarryRange k : ℤ))
            (cfzCarryRange k : ℤ),
          (affineStripInBox N (cfzBlockVariation k D)
            (cfzAffineForm q) ((N : ℤ) * c)).card := by
      exact Finset.card_biUnion_le
    _ ≤
        ∑ _c ∈ Finset.Icc (-(cfzCarryRange k : ℤ))
            (cfzCarryRange k : ℤ),
          ((2 * cfzBlockVariation k D + 1) *
            N ^ (Fintype.card (CFZVariable k) - 1)) := by
      exact Finset.sum_le_sum fun c _hc => hstrip c
    _ =
        (2 * cfzCarryRange k + 1) *
          (2 * cfzBlockVariation k D + 1) *
          N ^ (Fintype.card (CFZVariable k) - 1) := by
      have hcard :
          (Finset.Icc (-(cfzCarryRange k : ℤ))
              (cfzCarryRange k : ℤ)).card =
            2 * cfzCarryRange k + 1 := by
        rw [Int.card_Icc]
        norm_num
        rw [show
          (cfzCarryRange k : ℤ) + 1 +
              (cfzCarryRange k : ℤ) =
            ((2 * cfzCarryRange k + 1 : ℕ) : ℤ) by
              push_cast
              ring]
        exact Int.toNat_natCast _
      rw [Finset.sum_const, Nat.nsmul_eq_mul, hcard]
      ring
