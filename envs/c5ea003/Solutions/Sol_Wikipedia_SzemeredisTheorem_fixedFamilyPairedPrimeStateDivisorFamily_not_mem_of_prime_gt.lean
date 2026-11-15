-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.fixedFamilyPairedPrimeStateDivisorFamily_not_mem_of_prime_gt
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:52:28.454999+00:00
-- url     : https://prove2.me/submissions/a482734f-419a-4e1d-97c1-38b325cde311

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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Full-space cancellation of the canonical divisor truncation error

Fourier inversion sees the unrestricted primewise divisor expansion as a
finite sum over squarefree paired divisor families.  Terms whose left or
right divisor has crossed the coordinatewise cutoff have zero full-space
integral, because the smooth cutoff is supported in `(-∞, 1)`.  Thus the
unrestricted integral is exactly the coordinatewise-truncated integral.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff





end SmoothSieveCutoff

/-! ## The three paired states at every active prime/form incidence -/













/-! ## The squarefree divisor family encoded by a state assignment -/





@[simp]
theorem mem_fixedFamilyPairedPrimeStateLeftPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateLeftPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  classical
  simp [fixedFamilyPairedPrimeStateLeftPrimes]

@[simp]
theorem mem_fixedFamilyPairedPrimeStateRightPrimes
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    p ∈ fixedFamilyPairedPrimeStateRightPrimes support A q ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  classical
  simp [fixedFamilyPairedPrimeStateRightPrimes]





















theorem prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem
    {P : Finset Nat.Primes}
    (s : Finset {p // p ∈ P}) (p : {p // p ∈ P}) :
    (p : ℕ) ∣ ∏ r ∈ s, (r : ℕ) ↔ p ∈ s := by
  constructor
  · intro hp
    obtain ⟨r, hr, hpr⟩ :=
      (p.1.prop.prime.dvd_finsetProd_iff
        (fun r : {p // p ∈ P} => (r : ℕ))).mp hp
    have heqNat : (r : ℕ) = (p : ℕ) :=
      (r.1.prop.dvd_iff_eq p.1.prop.ne_one).mp hpr
    have heq : r = p := by
      apply Subtype.ext
      apply Subtype.ext
      exact heqNat
    simpa [heq] using hr
  · intro hp
    exact Finset.dvd_prod_of_mem
      (fun r : {p // p ∈ P} => (r : ℕ)) hp

theorem prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    (p : ℕ) ∣
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 1 := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  rw [
    prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem,
    mem_fixedFamilyPairedPrimeStateLeftPrimes]

theorem prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) (p : {p // p ∈ P}) :
    (p : ℕ) ∣
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 ↔
      ∃ hq : q ∈ support p, A p ⟨q, hq⟩ ≠ 0 := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  rw [
    prime_dvd_fixedFamilyPairedPrimeStatePrimeProduct_iff_mem,
    mem_fixedFamilyPairedPrimeStateRightPrimes]

















theorem fixedFamilyPairedPrimeStateDivisorFamily_pos
    {κ : Type*} [Fintype κ]
    {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (q : κ) :
    0 <
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ∧
      0 <
        (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 := by
  classical
  unfold fixedFamilyPairedPrimeStateDivisorFamily
  constructor <;>
    exact Finset.prod_pos fun p _hp => p.1.prop.pos













/-! ## Fourier integration of one support fiber -/

















end Wikipedia.SzemeredisTheorem

end
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
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators
/-! ## Integer coefficient geometry of canonical carry vectors -/
/-! ## The honest complete support series and Euler integrand -/
/-! ## Expanding one active prime support into nonempty form supports -/
/-! ## A large active prime is killed by full-space Fourier inversion -/

open Wikipedia.SzemeredisTheorem in
/-- If an active prime is larger than the coordinatewise divisor cutoff,
every three-state refinement places it in at least one divisor and hence
lies outside the smooth divisor box. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {R : ℕ} {P : Finset Nat.Primes}
    (support : FixedFamilyPrimeSupportAssignment κ P)
    (A : FixedFamilyPairedPrimeStateAssignment support)
    (p : {p // p ∈ P})
    (hpSupport : (support p).Nonempty)
    (hpR : R < (p : ℕ)) :
    fixedFamilyPairedPrimeStateDivisorFamily support A ∉
      smoothDivisorFamilyChoices κ R := by
  intro hz
  obtain ⟨q, hq⟩ := hpSupport
  have hqPair :
      fixedFamilyPairedPrimeStateDivisorFamily support A q ∈
        smoothDivisorPairChoices R :=
    Fintype.mem_piFinset.mp hz q
  have hqSides := Finset.mem_product.mp hqPair
  have hleftLe :
      (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 ≤ R :=
    (Finset.mem_Icc.mp hqSides.1).2
  have hrightLe :
      (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 ≤ R :=
    (Finset.mem_Icc.mp hqSides.2).2
  have hpos :=
    fixedFamilyPairedPrimeStateDivisorFamily_pos support A q
  by_cases hstate : A p ⟨q, hq⟩ = 1
  · have hneZero : A p ⟨q, hq⟩ ≠ 0 := by
      intro hzero
      rw [hzero] at hstate
      norm_num at hstate
    have hpDvd :
        (p : ℕ) ∣
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 :=
      (prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_right_iff
        support A q p).2 ⟨hq, hneZero⟩
    have hpLe :
        (p : ℕ) ≤
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).2 :=
      Nat.le_of_dvd hpos.2 hpDvd
    omega
  · have hpDvd :
        (p : ℕ) ∣
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 :=
      (prime_dvd_fixedFamilyPairedPrimeStateDivisorFamily_left_iff
        support A q p).2 ⟨hq, hstate⟩
    have hpLe :
        (p : ℕ) ≤
          (fixedFamilyPairedPrimeStateDivisorFamily support A q).1 :=
      Nat.le_of_dvd hpos.1 hpDvd
    omega
