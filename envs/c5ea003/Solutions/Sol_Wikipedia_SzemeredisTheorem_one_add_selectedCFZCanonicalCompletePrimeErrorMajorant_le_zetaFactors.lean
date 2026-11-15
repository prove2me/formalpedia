-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.one_add_selectedCFZCanonicalCompletePrimeErrorMajorant_le_zetaFactors
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:25:05.546216+00:00
-- url     : https://prove2.me/submissions/d1eff2a4-91da-4228-abd9-32715684c8a9

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletionTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_PrimeHarmonicProductBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_UnrestrictedPrimeSupportEulerSeries
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Normed.Ring.InfiniteProd
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_primeEulerFactor_ofReal
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_add_nat_mul_add_nat_mul_le_inv_one_sub_pow_mul

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Polylogarithmic control of the canonical Euler-completion tail

The complete-support majorant has local factor

`1 + 3m p^(-1-1/log R) + 4^m p^(-2)`,

where `m` is the number of selected CFZ forms.  We compare its two
nonconstant pieces with the Euler products for
`ζ(1 + 1 / log R)` and `ζ(2)`.  The elementary bound
`‖ζ(1 + 1 / log R)‖ ≤ 1 + log R` then gives an explicit
polylogarithmic bound for the whole infinite support mass, and hence for
the genuinely missing completion tail.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators
/-! ## A two-factor Euler comparison -/

open Wikipedia.SzemeredisTheorem in
/-- The local completion-majorant factor is bounded by the product of
the shifted and square zeta Euler factors. -/
theorem solution
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) (p : Nat.Primes) :
    1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p ≤
      ‖(1 - (p : ℂ) ^
          (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^
          (3 * Fintype.card (SelectedCFZFormIndex e)) *
        ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^
          (4 ^ Fintype.card (SelectedCFZFormIndex e)) := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  let x : ℝ :=
    (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹ - 1)
  let y : ℝ := (p : ℝ) ^ (-2 : ℝ)
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hshift : 0 < 1 + (Real.log (R : ℝ))⁻¹ := by
    positivity
  have hpOne : (1 : ℝ) < p := by exact_mod_cast p.prop.two_le
  have hx0 : 0 ≤ x := by
    unfold x
    positivity
  have hx1 : x < 1 := by
    unfold x
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl
      ⟨hpOne, by
        have hinv : 0 < (Real.log (R : ℝ))⁻¹ := inv_pos.mpr hlog
        linarith⟩)
  have hy0 : 0 ≤ y := by
    unfold y
    positivity
  have hy1 : y < 1 := by
    unfold y
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl ⟨hpOne, by norm_num⟩)
  have hlocal :=
    one_add_nat_mul_add_nat_mul_le_inv_one_sub_pow_mul
      (3 * m) (4 ^ m) hx0 hx1 hy0 hy1
  have hxFactor :
      (1 - x)⁻¹ =
        ‖(1 - (p : ℂ) ^
          (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ := by
    rw [norm_primeEulerFactor_ofReal p.prop.two_le hshift]
    congr 2
    unfold x
    congr 1
    ring
  have hyFactor :
      (1 - y)⁻¹ =
        ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ := by
    rw [norm_primeEulerFactor_ofReal p.prop.two_le (by norm_num)]
  unfold selectedCFZCanonicalCompletePrimeErrorMajorant
  change
    1 + ((3 : ℝ) * (m : ℝ) * x +
      (4 : ℝ) ^ m / (p : ℝ) ^ 2) ≤ _
  have hyDiv :
      (4 : ℝ) ^ m / (p : ℝ) ^ 2 =
        ((4 ^ m : ℕ) : ℝ) * y := by
    unfold y
    rw [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv,
      Real.rpow_neg (by positivity), Real.rpow_two]
  rw [hxFactor, hyFactor] at hlocal
  calc
    1 + ((3 : ℝ) * (m : ℝ) * x +
        (4 : ℝ) ^ m / (p : ℝ) ^ 2) =
        1 + (((3 * m : ℕ) : ℝ) * x) +
          (((4 ^ m : ℕ) : ℝ) * y) := by
      rw [hyDiv]
      push_cast
      ring
    _ ≤ _ := by simpa [m] using hlocal
