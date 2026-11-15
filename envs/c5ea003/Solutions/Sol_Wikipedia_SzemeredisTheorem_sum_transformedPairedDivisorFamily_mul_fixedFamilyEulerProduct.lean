-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.sum_transformedPairedDivisorFamily_mul_fixedFamilyEulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:47:18.13425+00:00
-- url     : https://prove2.me/submissions/8afd97af-e987-459f-b9f8-87adc6c70941

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_sum_transformedPairedDivisorFamily_eq_squarefree
import Theorems.Thm_Wikipedia_SzemeredisTheorem_fixedFamilyPrimeSupportDensity_assignmentOf_eq_eulerProduct
import Theorems.Thm_Wikipedia_SzemeredisTheorem_sum_coordinatewiseTruncatedSupportCoefficient_mul_density

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# A finite Euler majorant for the carry harmonic LCM mass

The divisor cutoff in `smoothDivisorFamilyChoices κ R` is imposed on every
individual divisor.  It therefore couples the prime choices and does not
give an exact Euler product.  This file uses only the honest one-sided
comparison: a squarefree paired divisor family is injected into the larger
space in which, independently for every prime `p ≤ R`, an arbitrary subset
of the `2 * card κ` divisor occurrences may contain `p`.

The empty subset has weight one.  Every nonempty subset has weight `p⁻¹`,
because `p` then occurs in the global LCM.  Summing over the unrestricted
assignment space gives the finite product

`∏ p ∈ Nat.primesLE R, (1 + (2 ^ (2 * card κ) - 1) / p)`.

Only the injection into that space is used; no false equality with the
coordinatewise-truncated divisor family is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## Prime-occurrence assignments -/













/-! ## The unrestricted assignment sum -/





/-! ## Encoding supported divisor families -/



















/-! ## Möbius mass as the squarefree indicator -/







@[simp]
theorem mem_squarefreeSmoothPairedDivisorChoices
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {z : κ → ℕ × ℕ} :
    z ∈ squarefreeSmoothPairedDivisorChoices κ R ↔
      z ∈ smoothDivisorFamilyChoices κ R ∧
        SquarefreePairedDivisorChoice z := by
  classical
  simp [squarefreeSmoothPairedDivisorChoices]



/-! ## The harmonic LCM Euler majorant -/









/-! ## Selected and Selberg-scaled corollaries -/

















end SmoothSieveCutoff

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
/-- The original finite divisor sum is exactly the support-fiber sum.  This
is the finite divisor-sum reorganization; no Euler approximation has been
made. -/
theorem solution
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (forms : κ → AffineForm ι ℤ)
    (t u : κ → ℝ) :
    ∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z =
      ∑ support ∈
          fixedFamilyPrimeSupportAssignmentChoices
            κ (primesLEAsPrimes R),
        coordinatewiseTruncatedSupportCoefficient
            χ R (primesLEAsPrimes R) t u support *
          fixedFamilyPrimeSupportDensity forms support := by
  classical
  calc
    (∑ z ∈ smoothDivisorFamilyChoices κ R,
        χ.transformedPairedDivisorFamily R z (t, u) *
          fixedFamilyDivisorEulerProduct forms z) =
        ∑ z ∈
            SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
          χ.transformedPairedDivisorFamily R z (t, u) *
            fixedFamilyDivisorEulerProduct forms z :=
      χ.sum_transformedPairedDivisorFamily_eq_squarefree
        R (fixedFamilyDivisorEulerProduct forms) (t, u)
    _ = ∑ z ∈
            SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R,
          χ.transformedPairedDivisorFamily R z (t, u) *
            fixedFamilyPrimeSupportDensity forms
              (fixedFamilyPrimeSupportAssignmentOf
                (primesLEAsPrimes R) z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzData :=
        SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp hz
      rw [fixedFamilyDivisorEulerProduct,
        fixedFamilyPrimeSupportDensity_assignmentOf_eq_eulerProduct
          forms hzData.1 hzData.2]
    _ = _ :=
      (sum_coordinatewiseTruncatedSupportCoefficient_mul_density
        χ R forms (primesLEAsPrimes R) t u).symm
