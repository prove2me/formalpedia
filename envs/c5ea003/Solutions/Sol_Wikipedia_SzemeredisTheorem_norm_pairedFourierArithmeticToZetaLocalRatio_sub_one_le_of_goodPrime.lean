-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le_of_goodPrime
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:57:46.663228+00:00
-- url     : https://prove2.me/submissions/9c537da6-6d77-4356-be8e-51b5bbfc8ed8

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_pairedFourierLocalFactor_sub_firstOrder_le_of_goodPrime
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_fourth_le_norm_fourierZetaSystemEulerLocalFactor

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Uniform Euler tails on CFZ carry blocks

The carry-block reduction leaves a genuinely varying affine system.  The
paired divisor choice determines the block side length, the point of the
quotient block determines all carry constants, and all of these data may
vary with the asymptotic parameter.  This file keeps that dependence.

At a prime outside the primorial, carry corrections alter only affine
constants.  The direct modular one-form and rank-two predicates therefore
give the same `O_k(p⁻²)` arithmetic-to-zeta ratio estimate on every block,
uniformly in the divisor choice and in both Fourier variables.  The general
dominated Euler-product theorem then shows that the product over `p > w`
tends to one as `w → ∞`.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open scoped BigOperators
/-! ## A dependent package for a varying carry block -/
/-! ## Direct modular local estimate -/

open Wikipedia.SzemeredisTheorem in
/-- Direct modular version of the arithmetic/zeta ratio estimate.  It is
uniform in all affine constants and all Fourier variables. -/
theorem
    solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    {forms : κ → AffineForm ι ℤ}
    {R p : ℕ} [NeZero p]
    (hnonzero : AffineNonzeroGoodPrime p forms)
    (hrankTwo : AffineRankTwoGoodPrime p forms)
    (hR : 2 ≤ R)
    (hcut :
      complexZetaModelNonzeroCutoff
          (Fintype.card κ) ≤ p)
    (t u : κ → ℝ) :
    ‖pairedFourierArithmeticToZetaLocalRatio
          R p forms t u - 1‖ ≤
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card κ) /
        (p : ℝ) ^ 2 := by
  let zeta :=
    fourierZetaSystemEulerLocalFactor R p t u
  have hzetaQuarter :
      (1 : ℝ) / 4 ≤ ‖zeta‖ := by
    exact
      one_fourth_le_norm_fourierZetaSystemEulerLocalFactor
        hR hnonzero.1 hcut t u
  have hzetaPos : 0 < ‖zeta‖ :=
    (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      hzetaQuarter
  have hcomparison :
      complexZetaModelComparisonCutoff
          (Fintype.card κ) ≤ p :=
    (Nat.le_max_left _ _).trans hcut
  have hseven : 7 ≤ p :=
    (Nat.le_max_left 7
      (6 * Fintype.card κ)).trans hcomparison
  have harithmetic :=
    norm_pairedFourierLocalFactor_sub_firstOrder_le_of_goodPrime
      hnonzero hrankTwo hR t u
  have hzeta :=
    norm_fourierZetaSystemEulerLocalFactor_sub_firstOrder_le
      hR hnonzero.1 hseven t u
  have hdiff :
      ‖pairedFourierLocalFactor R p forms t u - zeta‖ ≤
        complexArithmeticZetaDifferenceConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
    have htriangle :
        ‖pairedFourierLocalFactor R p forms t u - zeta‖ ≤
          ‖pairedFourierLocalFactor R p forms t u -
              pairedFourierFirstOrderLocalModel R p t u‖ +
            ‖zeta -
              pairedFourierFirstOrderLocalModel R p t u‖ := by
      have hrearrange :
          pairedFourierLocalFactor R p forms t u - zeta =
            (pairedFourierLocalFactor R p forms t u -
                pairedFourierFirstOrderLocalModel R p t u) -
              (zeta -
                pairedFourierFirstOrderLocalModel R p t u) := by
        ring
      rw [hrearrange]
      exact norm_sub_le _ _
    calc
      ‖pairedFourierLocalFactor R p forms t u - zeta‖ ≤
          ‖pairedFourierLocalFactor R p forms t u -
              pairedFourierFirstOrderLocalModel R p t u‖ +
            ‖zeta -
              pairedFourierFirstOrderLocalModel R p t u‖ :=
        htriangle
      _ ≤
          (4 : ℝ) ^ Fintype.card κ / (p : ℝ) ^ 2 +
            complexZetaModelDifferenceConstant
                (Fintype.card κ) /
              (p : ℝ) ^ 2 :=
        add_le_add harithmetic (by simpa [zeta] using hzeta)
      _ =
          complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2 := by
        rw [complexArithmeticZetaDifferenceConstant]
        ring
  have hzetaNe : zeta ≠ 0 :=
    norm_pos_iff.mp hzetaPos
  rw [pairedFourierArithmeticToZetaLocalRatio,
    div_sub_one hzetaNe, Complex.norm_div]
  calc
    ‖pairedFourierLocalFactor R p forms t u - zeta‖ /
          ‖zeta‖ ≤
        4 *
          ‖pairedFourierLocalFactor R p forms t u - zeta‖ := by
      rw [div_le_iff₀ hzetaPos]
      have hnonneg :
          0 ≤ ‖pairedFourierLocalFactor R p forms t u - zeta‖ :=
        norm_nonneg _
      nlinarith
    _ ≤
        4 *
          (complexArithmeticZetaDifferenceConstant
              (Fintype.card κ) /
            (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdiff (by norm_num)
    _ =
        complexArithmeticZetaRatioErrorConstant
            (Fintype.card κ) /
          (p : ℝ) ^ 2 := by
      rw [complexArithmeticZetaRatioErrorConstant]
      ring
