-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass_le_polylog
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:53:30.099503+00:00
-- url     : https://prove2.me/submissions/63eefc35-23cd-4665-b8f1-9bc02350b859

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_abs_normalizedSelbergScale_mul_logSq_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_normalizer_pos
import Theorems.Thm_Wikipedia_SzemeredisTheorem_selectedCFZCanonicalCompleteSupportMass_le_polylog

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Complete Euler series for the canonical carry model

The canonical divisor expansion naturally produces a finite Euler product
over the primes at most the Selberg radius.  This file defines the honest
complete prime-support series, identifies it with the existing paired
Fourier Euler product, and compares its Fourier integral with the finite
prime-support expression.

There are two logically separate convergence statements.

* At each fixed Fourier frequency the support series is absolutely
  convergent.  In the selected CFZ primorial regime this follows from the
  exact integer coefficient geometry proved below.
* After multiplication by the paired Schwartz envelope, the series is
  absolutely summable in `L¹`.  This is what permits termwise Fourier
  inversion.  It is stronger than pointwise absolute convergence and is
  proved explicitly below rather than inferred from a pointwise `tsum`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Topology
open scoped BigOperators

/-! ## Integer coefficient geometry of canonical carry vectors -/





/-! ## The honest complete support series and Euler integrand -/













/-! ## Expanding one active prime support into nonempty form supports -/











/-! ## A large active prime is killed by full-space Fourier inversion -/





/-! ## A summable uniform majorant and `L¹` convergence -/



theorem selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (p : Nat.Primes) :
    0 ≤ selectedCFZCanonicalCompletePrimeErrorMajorant e R p := by
  unfold selectedCFZCanonicalCompletePrimeErrorMajorant
  positivity







theorem selectedCFZCanonicalCompleteSupportMajorant_nonneg
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (S : Finset Nat.Primes) :
    0 ≤ selectedCFZCanonicalCompleteSupportMajorant e R S := by
  unfold selectedCFZCanonicalCompleteSupportMajorant
  exact Finset.prod_nonneg fun p _hp =>
    selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R p









/-! ## The completion tail as one absolutely convergent series -/





















/-! ## Exact remaining interface for diagonal growing-box decay -/



theorem selectedCFZCanonicalCompleteSupportMass_nonneg
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) :
    0 ≤ selectedCFZCanonicalCompleteSupportMass e R := by
  unfold selectedCFZCanonicalCompleteSupportMass
  exact tsum_nonneg fun S =>
    selectedCFZCanonicalCompleteSupportMajorant_nonneg e R S













end Wikipedia.SzemeredisTheorem

end
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
/-! ## The infinite support mass -/
/-! ## Pointwise and complementary-box bounds -/
/-! ## The completed Euler model on the complementary box -/
/-! ## Selberg-scaled complementary contributions -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- Uniform scaled polylogarithmic mass bound.  It is independent of
`N` and of the reduced residue. -/
theorem
    solution
    {k : ℕ} (χ : SmoothSieveCutoff)
    (w : ℕ) (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    χ.selectedCFZCanonicalCompleteEulerScaledSupportMass w R e ≤
      χ.selectedCFZCanonicalCompleteEulerScaledPolylogConstant e *
        (1 + Real.log R) ^
          selectedCFZCanonicalCompleteEulerScaledPolylogExponent e := by
  let m := Fintype.card (SelectedCFZFormIndex e)
  let E := selectedCFZCanonicalCompleteSupportPolylogExponent e
  let C := selectedCFZCanonicalCompleteSupportPolylogConstant e
  have hbase :
      |normalizedSelbergScale
          χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| ≤
        χ.normalizer⁻¹ * (1 + Real.log R) :=
    χ.abs_normalizedSelbergScale_mul_logSq_le hR w
  have hbaseNonneg :
      0 ≤
        |normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2| := by positivity
  have hlogNonneg : 0 ≤ 1 + Real.log R := by
    have hlog :
        0 ≤ Real.log R :=
      (Real.log_pos
        (by exact_mod_cast hR : (1 : ℝ) < R)).le
    linarith
  have hupperBaseNonneg :
      0 ≤ χ.normalizer⁻¹ * (1 + Real.log R) :=
    mul_nonneg
      (inv_nonneg.mpr χ.normalizer_pos.le) hlogNonneg
  have hmass :
      selectedCFZCanonicalCompleteSupportMass e R ≤
        C * (1 + Real.log R) ^ E := by
    simpa only [C, E] using
      selectedCFZCanonicalCompleteSupportMass_le_polylog e hR
  have hmassNonneg :
      0 ≤ selectedCFZCanonicalCompleteSupportMass e R :=
    selectedCFZCanonicalCompleteSupportMass_nonneg e R
  unfold
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledSupportMass
    SmoothSieveCutoff.selectedCFZCanonicalCompleteEulerScaledPolylogConstant
    selectedCFZCanonicalCompleteEulerScaledPolylogExponent
  change
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
        |Real.log R ^ 2| ^ m *
        selectedCFZCanonicalCompleteSupportMass e R ≤
      (χ.normalizer⁻¹ ^ m * C) *
        (1 + Real.log R) ^ (m + E)
  calc
    |normalizedSelbergScale χ.normalizer R (primorial w)| ^ m *
          |Real.log R ^ 2| ^ m *
          selectedCFZCanonicalCompleteSupportMass e R =
        (|normalizedSelbergScale
            χ.normalizer R (primorial w)| *
          |Real.log R ^ 2|) ^ m *
          selectedCFZCanonicalCompleteSupportMass e R := by
      rw [mul_pow]
    _ ≤
        (χ.normalizer⁻¹ * (1 + Real.log R)) ^ m *
          (C * (1 + Real.log R) ^ E) :=
      mul_le_mul
        (pow_le_pow_left₀ hbaseNonneg hbase m)
        hmass hmassNonneg
        (pow_nonneg hupperBaseNonneg m)
    _ =
        (χ.normalizer⁻¹ ^ m * C) *
          (1 + Real.log R) ^ (m + E) := by
      rw [mul_pow, pow_add]
      ring
