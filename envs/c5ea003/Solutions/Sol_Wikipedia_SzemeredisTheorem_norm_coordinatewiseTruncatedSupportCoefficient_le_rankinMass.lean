-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_coordinatewiseTruncatedSupportCoefficient_le_rankinMass
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:22:29.090956+00:00
-- url     : https://prove2.me/submissions/44e197a6-af54-49cb-aa88-f184a3839f4d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorTruncation
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_transformedPairedDivisorFamily_eq_rankin

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

section


/-!
# Canonical divisor truncation bounds

This file closes the purely infinite-series part of the canonical
fixed-carry expansion and isolates the genuinely coordinatewise part.

For a fixed prime-local factor with summable local errors, the sums over
subsets of the primes at most `X` converge to the full unrestricted
prime-support series.  This applies in particular to every fixed
carry-adjusted affine family satisfying the usual coefficient hypotheses.

The remaining divisor-cutoff discrepancy is bounded fiberwise by an
explicit finite quantity: the number of coordinatewise-admissible
squarefree divisor families in the support fiber, plus the unrestricted
primewise coefficient majorant.  Thus no infinite-series truncation remains
hidden in that discrepancy.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-! ## Exhaustion of natural primes -/







/-! ## Finite powersets converge to the unrestricted support series -/





/-! ## Fixed canonical carry families -/









/-! ## Coordinatewise support-fiber bounds -/



theorem mem_coordinatewiseTruncatedSupportFiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {P : Finset Nat.Primes}
    {support : FixedFamilyPrimeSupportAssignment κ P}
    {z : κ → ℕ × ℕ} :
    z ∈ coordinatewiseTruncatedSupportFiber R P support ↔
      z ∈ SmoothSieveCutoff.squarefreeSmoothPairedDivisorChoices κ R ∧
        fixedFamilyPrimeSupportAssignmentOf P z = support := by
  classical
  simp [coordinatewiseTruncatedSupportFiber]



theorem coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    coordinatewiseTruncatedSupportCoefficient
        χ R P t u support =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        χ.transformedPairedDivisorFamily R z (t, u) := by
  classical
  rfl















/-! ## The named carry-weighted truncation majorant -/









end Wikipedia.SzemeredisTheorem

end
/-!
# Rankin bounds for canonical coordinatewise divisor truncation

The pointwise cardinality majorant for the canonical divisor-cutoff
discrepancy is much too large.  This file retains the actual norms of all
divisor phases and paired Fourier prime coefficients.

There is an important scale distinction.  The norm of a divisor phase is

`d ^ (-1 / log R)`.

Consequently a Rankin exponent compatible with prime summability is itself
of order `1 / log R`; its threshold gain is only a fixed exponential
constant.  Thus absolute values do not imply raw pointwise decay, even on a
growing Fourier box (the phase norm is frequency-independent).  The usable
result is instead a sharp arithmetic mass multiplying the common Schwartz
density.  Arbitrarily high Fourier moments then control the complementary
integral.  Cancellation of the full integral, coming from Fourier inversion
and compact support of the cutoff, is the separate interior step.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Topology
/-! ## Exact phase scale and the critical Rankin obstruction -/
/-! ## Actual coefficient and phase masses -/

open Wikipedia.SzemeredisTheorem in
/-- The exact coordinatewise coefficient is bounded by its phase-weighted
Rankin fiber mass, rather than by the raw fiber cardinality. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff)
    {R : ℕ} (hR : 1 < R)
    (P : Finset Nat.Primes) (t u : κ → ℝ)
    (support : FixedFamilyPrimeSupportAssignment κ P) :
    ‖coordinatewiseTruncatedSupportCoefficient
        χ R P t u support‖ ≤
      coordinatewiseTruncatedSupportRankinMass R P support *
        (χ.fourierProductMomentDensity (fun _ => 0) t *
          χ.fourierProductMomentDensity (fun _ => 0) u) := by
  classical
  rw [coordinatewiseTruncatedSupportCoefficient_eq_sum_fiber]
  calc
    ‖∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        χ.transformedPairedDivisorFamily R z (t, u)‖ ≤
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        ‖χ.transformedPairedDivisorFamily R z (t, u)‖ :=
      norm_sum_le _ _
    _ =
      ∑ z ∈ coordinatewiseTruncatedSupportFiber R P support,
        pairedDivisorRankinWeight R z *
          (χ.fourierProductMomentDensity (fun _ => 0) t *
            χ.fourierProductMomentDensity (fun _ => 0) u) := by
      apply Finset.sum_congr rfl
      intro z hzFiber
      have hzSquarefree :
          SquarefreePairedDivisorChoice z :=
        (SmoothSieveCutoff.mem_squarefreeSmoothPairedDivisorChoices.mp
          ((mem_coordinatewiseTruncatedSupportFiber.mp hzFiber).1)).2
      exact χ.norm_transformedPairedDivisorFamily_eq_rankin
        hR z hzSquarefree t u
    _ = _ := by
      unfold coordinatewiseTruncatedSupportRankinMass
      rw [Finset.sum_mul]
