-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletion
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalEulerCompletion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T09:20:49.893097+00:00
-- url     : https://prove2.me/theorems/34362acf-8815-4c29-b0bb-21b9650f8e4d
-- title:
--   Complete canonical carry Euler series and completion discrepancy
-- statement:
--   For a finite index type $\kappa$ with decidable equality, natural parameters $N,W,b,R$, a family of CFZ forms, an integer carry vector, and paired real Fourier coordinates, this bundle defines the complete prime-support series by summing over all finite prime sets. When $N
--   e0$, it averages these series with canonical carry-cell densities and multiplies the result by the paired cutoff Fourier envelope of a smooth sieve cutoff $\chi$. The completion discrepancy is the finite support integrand minus this complete integrand.
--
--   For a selected CFZ pattern $e$ with $m$ forms, the frequency-independent local error majorant is $3m\,p^{-1-1/\log R}+4^m/p^2$. Products over finite prime supports and their total sum define the complete support majorant and mass. The tail index pairs an admissible carry vector with a finite prime support outside the powerset of primes at most $R$; its integrand has a minus sign, matching the finite-minus-complete convention.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/CFZCanonicalEulerCompletion.lean#L100-L1425

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorIntegralCancellation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalDivisorRankinTruncation
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryEulerTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrection
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Lean
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The full squarefree prime-support series for one canonical carry
vector.  Unlike the finite powerset in
`cfzCanonicalCarryUnrestrictedFourierAverage`, the support index ranges
over every finite set of natural primes. -/
noncomputable def cfzCanonicalCarryCompletePrimeSupportSeries
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ) : ℂ :=
  ∑' S : Finset Nat.Primes,
    unrestrictedPrimeSupportTerm
      (cfzCanonicalCarryPairedFourierPrimeLocalFactor
        N W b R forms carry t u) S

/-- Carry-weighted complete prime-support average. -/
noncomputable def cfzCanonicalCarryCompleteFourierAverage
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (t u : κ → ℝ) : ℂ :=
  ∑ carry ∈ cfzCanonicalCarryVectorChoices κ k,
    (cfzCanonicalCarryCellDensity
        (N := N) forms carry : ℂ) *
      cfzCanonicalCarryCompletePrimeSupportSeries
        N W b R forms carry t u

/-- The complete canonical carry Euler integrand.  It is written as a
support `tsum` inside each finite carry cell; later the `L¹` theorem
justifies integrating this pointwise series. -/
noncomputable def SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  pairedCutoffFourierEnvelope χ tu.1 tu.2 *
    cfzCanonicalCarryCompleteFourierAverage
      (N := N) W b R forms tu.1 tu.2

/-- Difference between the finite prime-support Euler integrand occurring
in the canonical divisor expansion and the honest complete support
integrand. -/
noncomputable def SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k N : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (W b R : ℕ) (forms : κ → CFZFormIndex k)
    (tu : (κ → ℝ) × (κ → ℝ)) : ℂ :=
  pairedCutoffFourierEnvelope χ tu.1 tu.2 *
      cfzCanonicalCarryUnrestrictedFourierAverage
        (N := N) W b R forms tu.1 tu.2 -
    χ.cfzCanonicalCarryCompleteEulerIntegrand
      (N := N) W b R forms tu





/-! ## Expanding one active prime support into nonempty form supports -/

/-- Form-support assignments in which every prime of `P` is genuinely
active.  This is the support-assignment counterpart of one term indexed by
`P : Finset Nat.Primes` in `unrestrictedPrimeSupportTerm`. -/
def fixedFamilyNonemptyPrimeSupportAssignmentChoices
    (κ : Type*) [Fintype κ] [DecidableEq κ]
    (P : Finset Nat.Primes) :
    Finset (FixedFamilyPrimeSupportAssignment κ P) :=
  Fintype.piFinset fun _p : {p // p ∈ P} =>
    (Finset.univ : Finset κ).powerset.erase ∅









/-! ## A large active prime is killed by full-space Fourier inversion -/





/-! ## A summable uniform majorant and `L¹` convergence -/

/-- Frequency-independent majorant for the selected canonical carry local
error.  The positive Fourier shift supplies the summable
`p^(-1-1/log R)` term; rank-two geometry supplies the reciprocal-square
remainder. -/
noncomputable def selectedCFZCanonicalCompletePrimeErrorMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (p : Nat.Primes) : ℝ :=
  (3 * Fintype.card (SelectedCFZFormIndex e) : ℝ) *
      (p : ℝ) ^ (-(Real.log (R : ℝ))⁻¹ - 1) +
    (4 : ℝ) ^ Fintype.card (SelectedCFZFormIndex e) /
      (p : ℝ) ^ 2







/-- Product majorant for one finite active-prime support. -/
noncomputable def selectedCFZCanonicalCompleteSupportMajorant
    {k : ℕ} (e : LinearFormsExponent k)
    (R : ℕ) (S : Finset Nat.Primes) : ℝ :=
  ∏ p ∈ S,
    selectedCFZCanonicalCompletePrimeErrorMajorant e R p











/-! ## The completion tail as one absolutely convergent series -/



/-- The countable index set for the missing completion tail: a canonical
carry cell together with a finite prime support which is not contained in
the finite Euler set `p ≤ R`. -/
def SelectedCFZCanonicalCarryEulerCompletionTailIndex
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) : Type :=
  {carry : SelectedCFZFormIndex e → ℤ //
      carry ∈ cfzCanonicalCarryVectorChoices
        (SelectedCFZFormIndex e) k} ×
    ↥
      ((↑((primesLEAsPrimes R).powerset) :
        Set (Finset Nat.Primes))ᶜ)

/-- One signed term of the full completion tail.  The minus sign records
`finite Euler series - complete Euler series`. -/
noncomputable def SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (e : LinearFormsExponent k) (R : ℕ)
    (idx : SelectedCFZCanonicalCarryEulerCompletionTailIndex e R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) : ℂ :=
  -((cfzCanonicalCarryCellDensity
        (N := N)
        (fun q : SelectedCFZFormIndex e => q.1)
        idx.1.1 : ℂ) *
      (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N (primorial w) b R
            (fun q : SelectedCFZFormIndex e => q.1)
            idx.1.1 tu.1 tu.2) idx.2.1))















/-! ## Exact remaining interface for diagonal growing-box decay -/

/-- Total mass of the frequency-independent complete-support majorant. -/
noncomputable def selectedCFZCanonicalCompleteSupportMass
    {k : ℕ} (e : LinearFormsExponent k) (R : ℕ) : ℝ :=
  ∑' S : Finset Nat.Primes,
    selectedCFZCanonicalCompleteSupportMajorant e R S















end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SelectedCFZCanonicalCarryEulerCompletionTailIndex.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand.congr_simp,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand.eq_1,
    `Wikipedia.SzemeredisTheorem.fixedFamilyNonemptyPrimeSupportAssignmentChoices.eq_1,
    `Wikipedia.SzemeredisTheorem.selectedCFZCanonicalCompletePrimeErrorMajorant.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


