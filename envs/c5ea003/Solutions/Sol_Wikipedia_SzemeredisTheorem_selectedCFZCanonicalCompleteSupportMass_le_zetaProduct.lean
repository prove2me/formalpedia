-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.selectedCFZCanonicalCompleteSupportMass_le_zetaProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:42.264563+00:00
-- url     : https://prove2.me/submissions/028d73f4-da94-48fe-91ac-c0d7788b4437

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_one_add_selectedCFZCanonicalCompletePrimeErrorMajorant_le_zetaFactors
import Theorems.Thm_Wikipedia_SzemeredisTheorem_summable_selectedCFZCanonicalCompletePrimeErrorMajorant

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section






/-!
# Polylogarithmic bounds for a finite prime Euler product

This file bounds

`∏ p ∈ Nat.primesLE R, (1 + A / p)`.

The elementary comparison with the full harmonic sum gives an exponential
bound.  More importantly for Fourier-tail estimates, shifting the Euler
product of the Riemann zeta function to

`s = 1 + 1 / log R`

gives a polynomial bound in `log R`.  This avoids requiring a separately
formalized Mertens theorem.
-/

/-
The two integral-test lemmas below are backported from
Mathlib/Analysis/SumIntegralComparisons.lean at
db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson, Alastair Irving
-/
section GreenTaoIntegralTestCompatibility

open Set MeasureTheory MeasureSpace intervalIntegral
open scoped BigOperators

variable {f : ℝ → ℝ}





end GreenTaoIntegralTestCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter Set
open scoped BigOperators Topology













theorem one_le_norm_primeEulerFactor_ofReal
    {p : ℕ} (hp : 2 ≤ p) {s : ℝ} (hs : 0 < s) :
    1 ≤ ‖(1 - (p : ℂ) ^ (-((s : ℝ) : ℂ)))⁻¹‖ := by
  rw [norm_primeEulerFactor_ofReal hp hs]
  have hxlt : (p : ℝ) ^ (-s) < 1 := by
    rw [Real.rpow_lt_one_iff (by positivity)]
    exact Or.inr (Or.inl
      ⟨(by exact_mod_cast hp : (1 : ℝ) < p), by linarith⟩)
  exact (one_le_inv₀ (sub_pos.mpr hxlt)).2
    (by
      have hxnonneg :=
        Real.rpow_nonneg (show (0 : ℝ) ≤ p by positivity) (-s)
      linarith)























end Wikipedia.SzemeredisTheorem

end

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









/-- The support majorants are summable over all finite prime sets. -/
theorem summable_selectedCFZCanonicalCompleteSupportMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    Summable
      (selectedCFZCanonicalCompleteSupportMajorant e R) := by
  change Summable (fun S : Finset Nat.Primes =>
    ∏ p ∈ S,
      selectedCFZCanonicalCompletePrimeErrorMajorant e R p)
  exact
    summable_finsetProd_of_summable_nonneg
      (selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R)
      (summable_selectedCFZCanonicalCompletePrimeErrorMajorant e hR)







/-! ## The completion tail as one absolutely convergent series -/





















/-! ## Exact remaining interface for diagonal growing-box decay -/





/-- The complete-support majorant is itself the honest Euler product of
the nonnegative local majorants. -/
theorem selectedCFZCanonicalCompleteSupportMass_eq_tprod
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalCompleteSupportMass e R =
      ∏' p : Nat.Primes,
        (1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p) := by
  unfold selectedCFZCanonicalCompleteSupportMass
    selectedCFZCanonicalCompleteSupportMajorant
  exact
    (tprod_one_add
      (summable_selectedCFZCanonicalCompleteSupportMajorant
        e hR)).symm











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

open Wikipedia.SzemeredisTheorem in
/-- Explicit zeta-product bound for the full infinite completion-support
mass. -/
theorem solution
    {k : ℕ} (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R) :
    selectedCFZCanonicalCompleteSupportMass e R ≤
      ‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^
          selectedCFZCanonicalCompleteSupportPolylogExponent e *
        ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^
          (4 ^ Fintype.card (SelectedCFZFormIndex e)) := by
  let A := selectedCFZCanonicalCompleteSupportPolylogExponent e
  let B := 4 ^ Fintype.card (SelectedCFZFormIndex e)
  have hRone : (1 : ℝ) < R := by exact_mod_cast hR
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos hRone
  have hs :
      1 < ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)).re := by
    change (1 : ℝ) < 1 + (Real.log R)⁻¹
    have hinv : 0 < (Real.log R)⁻¹ := inv_pos.mpr hlog
    linarith
  have htwo : 1 < (((2 : ℝ) : ℂ)).re := by norm_num
  have hzetaShift :
      HasProd
        (fun p : Nat.Primes =>
          ‖(1 - (p : ℂ) ^
            (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A)
        (‖riemannZeta
          ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ A) :=
    (riemannZeta_eulerProduct_hasProd hs).norm.pow A
  have hzetaTwo :
      HasProd
        (fun p : Nat.Primes =>
          ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B)
        (‖riemannZeta ((2 : ℝ) : ℂ)‖ ^ B) :=
    (riemannZeta_eulerProduct_hasProd htwo).norm.pow B
  have hright :=
    hzetaShift.mul hzetaTwo
  have hleft :
      HasProd
        (fun p : Nat.Primes =>
          1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p)
        (selectedCFZCanonicalCompleteSupportMass e R) := by
    rw [selectedCFZCanonicalCompleteSupportMass_eq_tprod e hR]
    exact
      (multipliable_one_add_of_summable_prod
        (summable_selectedCFZCanonicalCompleteSupportMajorant
          e hR)).hasProd
  have hcomparison :
      selectedCFZCanonicalCompleteSupportMass e R ≤
        ‖riemannZeta
            ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ A *
          ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^ B := by
    apply hasProd_le_of_prod_le hleft
    intro s
    calc
      ∏ p ∈ s,
          (1 + selectedCFZCanonicalCompletePrimeErrorMajorant e R p) ≤
          ∏ p ∈ s,
            (‖(1 - (p : ℂ) ^
                (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A *
              ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B) := by
        apply Finset.prod_le_prod
        · intro p _hp
          have hnonneg :=
            selectedCFZCanonicalCompletePrimeErrorMajorant_nonneg e R p
          positivity
        · intro p _hp
          simpa [A, selectedCFZCanonicalCompleteSupportPolylogExponent, B]
            using
              one_add_selectedCFZCanonicalCompletePrimeErrorMajorant_le_zetaFactors
                e hR p
      _ ≤
          ‖riemannZeta
              ((((1 + (Real.log R)⁻¹ : ℝ)) : ℂ))‖ ^ A *
            ‖riemannZeta ((2 : ℝ) : ℂ)‖ ^ B := by
        apply ge_of_tendsto hright
        filter_upwards [eventually_ge_atTop s] with t hst
        apply Finset.prod_le_prod_of_subset_of_one_le hst
        · intro p _hp
          positivity
        · intro p _hpt _hps
          have hshiftPos :
              0 < 1 + (Real.log (R : ℝ))⁻¹ := by positivity
          have honeShift :
              1 ≤
                ‖(1 - (p : ℂ) ^
                  (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A :=
            one_le_pow₀
              (one_le_norm_primeEulerFactor_ofReal
                p.prop.two_le hshiftPos)
          have honeTwo :
              1 ≤
                ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B :=
            one_le_pow₀
              (one_le_norm_primeEulerFactor_ofReal
                p.prop.two_le (by norm_num))
          calc
            1 = 1 * 1 := by ring
            _ ≤
                ‖(1 - (p : ℂ) ^
                  (-(((1 + (Real.log R)⁻¹ : ℝ)) : ℂ)))⁻¹‖ ^ A *
                ‖(1 - (p : ℂ) ^ (-((2 : ℝ) : ℂ)))⁻¹‖ ^ B :=
              mul_le_mul honeShift honeTwo (by positivity) (by positivity)
  simpa [A, B, selectedCFZCanonicalCompleteSupportPolylogExponent] using
    hcomparison
