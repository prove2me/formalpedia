-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_euler_add_discrepancy
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:42.334691+00:00
-- url     : https://prove2.me/submissions/172b547a-5b88-46b1-a489-d31a0e3360d8

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryBlockEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
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
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Theorems.Thm_Wikipedia_SzemeredisTheorem_complexWeightedLocalFactor_eq_inclusionExclusion
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Canonical fixed-carry divisor expansions

On a canonical CFZ carry cell the affine family is fixed before the
divisor variables are chosen.  This file reorganizes the coordinatewise
truncated, squarefree paired-divisor sum by its prime-to-form supports.

The reorganization is exact.  The corresponding unrestricted support
sum factors into the existing paired Fourier local factors, and hence into
the finite-prime-support Euler series.  The difference between these two
finite sums is recorded explicitly; it is precisely the remaining
coordinatewise-truncation splice, with no divisor-dependent affine family.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-! ## Generic finite prime-support assignments -/

























/-! ## Exact unrestricted finite Euler factorization -/

/-- One paired Fourier local factor is exactly its support sum. -/
theorem pairedFourierPrimeLocalFactor_eq_fixedFamilySupportSum
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) (p : Nat.Primes) :
    pairedFourierPrimeLocalFactor R forms t u p =
      ∑ s ∈ (Finset.univ : Finset κ).powerset,
        fixedFamilyPrimeLocalSupportTerm R forms t u p s := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  unfold pairedFourierPrimeLocalFactor pairedFourierLocalFactor
    fixedFamilyPrimeLocalSupportTerm
    fixedFamilyPrimeLocalCoefficient
  exact
    complexWeightedLocalFactor_eq_inclusionExclusion
      (p : ℕ) forms
      (fun q =>
        pairedFourierPrimeCoefficient
          R (p : ℕ) (t q) (u q))

/-- Summing all form-support assignments factors prime by prime. -/
theorem sum_fixedFamilyPrimeSupportEulerTerm_eq_prod_localFactors
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (R : ℕ) (forms : κ → AffineForm ι ℤ)
    (P : Finset Nat.Primes) (t u : κ → ℝ) :
    ∑ support ∈ fixedFamilyPrimeSupportAssignmentChoices κ P,
        fixedFamilyPrimeSupportEulerTerm
          R forms P t u support =
      ∏ p : {p // p ∈ P},
        pairedFourierPrimeLocalFactor R forms t u p.1 := by
  classical
  simp_rw [
    pairedFourierPrimeLocalFactor_eq_fixedFamilySupportSum]
  unfold fixedFamilyPrimeSupportAssignmentChoices
    fixedFamilyPrimeSupportEulerTerm
  rw [Finset.prod_univ_sum]



/-! ## The exact coordinatewise-truncated support fibers -/











/-! ## Replacing the supported prime range by the CRT Euler product -/





/-! ## The exact truncated-to-unrestricted splice -/











/-! ## Canonical fixed-carry specialization -/











/-! ## The carry-weighted canonical endpoint -/











end Wikipedia.SzemeredisTheorem

end
/-!
# Canonical fixed-carry divisor expansions

On a canonical CFZ carry cell the affine family is fixed before the
divisor variables are chosen.  This file reorganizes the coordinatewise
truncated, squarefree paired-divisor sum by its prime-to-form supports.

The reorganization is exact.  The corresponding unrestricted support
sum factors into the existing paired Fourier local factors, and hence into
the finite-prime-support Euler series.  The difference between these two
finite sums is recorded explicitly; it is precisely the remaining
coordinatewise-truncation splice, with no divisor-dependent affine family.
-/
open Wikipedia.SzemeredisTheorem
open scoped ArithmeticFunction.Moebius BigOperators
/-! ## Generic finite prime-support assignments -/
/-! ## Exact unrestricted finite Euler factorization -/
/-! ## The exact coordinatewise-truncated support fibers -/
/-! ## Replacing the supported prime range by the CRT Euler product -/
/-! ## The exact truncated-to-unrestricted splice -/

open Wikipedia.SzemeredisTheorem in
/-- Exact fixed-family splice.  The first term is the honest finite Euler
product; the second is the complete coordinatewise-truncation discrepancy,
grouped by prime-to-form support. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z =
      pairedCutoffFourierEnvelope χ t u *
          ∏ p :
              {p // p ∈ primesLEAsPrimes R},
            pairedFourierPrimeLocalFactor R forms t u p.1 +
        ∑ support ∈
            fixedFamilyPrimeSupportAssignmentChoices
              κ (primesLEAsPrimes R),
          coordinatewiseTruncationSupportDiscrepancy
              χ R (primesLEAsPrimes R) t u support *
            fixedFamilyPrimeSupportDensity forms support := by
  classical
  rw [
    sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct,
    ← sum_fixedFamilyPrimeSupportEulerTerm_eq_prod_localFactors
      R forms (primesLEAsPrimes R) t u]
  simp_rw [
    fixedFamilyPrimeSupportEulerTerm_eq_coefficient_mul_density]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro support _hsupport
  unfold coordinatewiseTruncationSupportDiscrepancy
  ring
