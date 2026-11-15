-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_transformedPairedDivisorFamily_mul_fixedEulerProduct_eq_unrestricted_add_discrepancy
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:50:06.233125+00:00
-- url     : https://prove2.me/submissions/7c0a905b-ca49-4328-8feb-ab5fc3b815ce

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_euler_add_discrepancy

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



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

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Generic absolutely convergent support expansion -/





/-- On a fixed finite prime set, summing over all active sub-supports gives
the corresponding finite Euler product. -/
theorem sum_unrestrictedPrimeSupportTerm_powerset
    (localFactor : Nat.Primes → ℂ)
    (P : Finset Nat.Primes) :
    ∑ S ∈ P.powerset,
        unrestrictedPrimeSupportTerm localFactor S =
      ∏ p ∈ P, localFactor p := by
  rw [show
      (∑ S ∈ P.powerset,
          unrestrictedPrimeSupportTerm localFactor S) =
        ∏ p ∈ P, (1 + (localFactor p - 1)) by
      simpa [unrestrictedPrimeSupportTerm] using
        (Finset.prod_one_add
          (s := P) (f := fun p => localFactor p - 1)).symm]
  apply Finset.prod_congr rfl
  intro p _hp
  ring







/-! ## Absolute convergence of paired-Fourier local errors -/











/-! ## Direct-good-prime and carry-block versions -/





namespace SelectedCFZCarryFourierBlockData











end SelectedCFZCarryFourierBlockData

/-! ## Exact paired-Fourier specialization -/





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
/-- The same splice with the Euler term written as the finite powerset
portion of the unrestricted prime-support series. -/
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
          ∑ S ∈ (primesLEAsPrimes R).powerset,
            unrestrictedPrimeSupportTerm
              (pairedFourierPrimeLocalFactor R forms t u) S +
        ∑ support ∈
            fixedFamilyPrimeSupportAssignmentChoices
              κ (primesLEAsPrimes R),
          coordinatewiseTruncationSupportDiscrepancy
              χ R (primesLEAsPrimes R) t u support *
            fixedFamilyPrimeSupportDensity forms support := by
  rw [
    sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct_eq_euler_add_discrepancy,
    sum_unrestrictedPrimeSupportTerm_powerset]
  exact
    congrArg
      (fun x =>
        pairedCutoffFourierEnvelope χ t u * x +
          ∑ support ∈
              fixedFamilyPrimeSupportAssignmentChoices
                κ (primesLEAsPrimes R),
            coordinatewiseTruncationSupportDiscrepancy
                χ R (primesLEAsPrimes R) t u support *
              fixedFamilyPrimeSupportDensity forms support)
      (Finset.prod_coe_sort
        (primesLEAsPrimes R)
        (pairedFourierPrimeLocalFactor R forms t u))
