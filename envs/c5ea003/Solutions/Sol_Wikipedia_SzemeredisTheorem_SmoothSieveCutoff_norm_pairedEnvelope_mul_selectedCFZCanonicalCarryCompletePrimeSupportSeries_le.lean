-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.norm_pairedEnvelope_mul_selectedCFZCanonicalCarryCompletePrimeSupportSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:59:51.311193+00:00
-- url     : https://prove2.me/submissions/adb01a78-a735-46f0-a08a-c7df596b9cf9

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_norm_selectedCFZCanonicalCarryCompleteSupportIntegrand_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
import Theorems.Thm_Wikipedia_SzemeredisTheorem_summable_norm_pairedFourierPrimeLocalFactor_sub_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_summable_selectedCFZCanonicalCompletePrimeErrorMajorant

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/

namespace Wikipedia.SzemeredisTheorem











@[simp]
theorem cfzCoefficient_selected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) =
      (i.1 : ℤ) - (q.1 : ℤ) := by
  simp [cfzCoefficient, i.2]





theorem cfzCoefficient_selected_ne_zero {k : ℕ}
    (q : CFZFormIndex k) (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) ≠ 0 := by
  rw [cfzCoefficient_selected]
  apply sub_ne_zero.mpr
  intro h
  apply i.2
  apply Fin.ext
  exact_mod_cast h

/-- For `k ≥ 2`, every CFZ form has a nonzero integer coefficient. -/
theorem exists_cfzCoefficient_ne_zero {k : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    ∃ v : CFZVariable k, cfzCoefficient q v ≠ 0 := by
  have hcard : 1 < Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨i, hi⟩ :=
    Fintype.exists_ne_of_one_lt_card hcard q.1
  let i' : {i : Fin k // i ≠ q.1} := ⟨i, hi⟩
  exact ⟨(i, q.2 i'), cfzCoefficient_selected_ne_zero q i'⟩

/-- Equivalently, the coefficient vector of every CFZ form is nonzero. -/
theorem cfzCoefficient_ne_zero {k : ℕ} (hk : 2 ≤ k)
    (q : CFZFormIndex k) :
    cfzCoefficient q ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_cfzCoefficient_ne_zero hk q
  intro hzero
  exact hv (congrFun hzero v)







end Wikipedia.SzemeredisTheorem

end

section



/-!
# Geometry of integer affine-form systems

The Goldston--Yıldırım estimate is stated for finite systems of integer
affine forms with nonzero, pairwise non-proportional coefficient vectors and
uniformly bounded coefficients.  This file packages those hypotheses and
verifies them for the Conlon--Fox--Zhao progression forms.
-/

namespace Wikipedia.SzemeredisTheorem

namespace AffineForm





end AffineForm











@[simp]
theorem cfzAffineForm_constant {k : ℕ} (q : CFZFormIndex k) :
    (cfzAffineForm q).constant = 0 :=
  rfl

@[simp]
theorem cfzAffineForm_coefficient {k : ℕ}
    (q : CFZFormIndex k) :
    (cfzAffineForm q).coefficient = cfzCoefficient q :=
  rfl









end Wikipedia.SzemeredisTheorem

end

section




/-!
# Small-prime local factors for W-tricked affine forms

If `ψ` is an integer affine form, the affine form occurring after the
`W`-trick is

`x ↦ W * ψ(x) + b`.

At a prime `p ∣ W` this form is identically `b` modulo `p`.  When `b` is a
reduced residue modulo `W`, it is therefore nowhere zero modulo `p`.  This
makes every small-prime avoidance factor, including the complex factor
produced by paired Fourier inversion, exactly one.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators



@[simp]
theorem wTrickedAffineForm_constant {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) :
    (wTrickedAffineForm W b ψ).constant =
      (W : ℤ) * ψ.constant + b :=
  rfl

@[simp]
theorem wTrickedAffineForm_coefficient {ι : Type*}
    (W b : ℕ) (ψ : AffineForm ι ℤ) (i : ι) :
    (wTrickedAffineForm W b ψ).coefficient i =
      (W : ℤ) * ψ.coefficient i :=
  rfl



























end Wikipedia.SzemeredisTheorem

end

section



/-!
# Carry-block boundaries for the cyclic CFZ lift

The standard representative of a CFZ form modulo `N` is not periodic in the
natural input coordinates.  This file gives the unconditional replacement
for the false periodicity step.

We divide the standard box into coordinatewise quotient blocks of side `D`.
On a block where every selected CFZ carry is constant, the cyclic lift is an
ordinary affine form with a carry-dependent constant.  A block on which one
carry changes must cross a hyperplane at an integral multiple of `N`.
Because CFZ coefficients are bounded and every CFZ form has a coefficient
equal to `1` or `-1`, the union of all such blocks has an explicit
codimension-one cardinality bound.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Coordinate quotient blocks -/



















/-! ## A generic unit-coefficient strip count -/









/-! ## CFZ coefficient and block-diameter facts -/





/-! ## Carry-change hyperplanes -/

























/-! ## Explicit bad-point counts -/

















/-! ## Carry-adjusted affine block model -/













@[simp]
theorem cfzCarryAdjustedAffineForm_coefficient
    {k : ℕ} (N W b : ℕ)
    (q : CFZFormIndex k) (c : ℤ)
    (v : CFZVariable k) :
    (cfzCarryAdjustedAffineForm N W b q c).coefficient v =
      (W : ℤ) * cfzCoefficient q v := by
  rfl

















/-! ## A normalized disagreement bound -/





















/-! ## Carry-dependent affine residue model -/















end Wikipedia.SzemeredisTheorem

end

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







/-- Absolute summability of the local errors implies absolute summability
of the series indexed by all finite prime supports. -/
theorem summable_unrestrictedPrimeSupportTerm
    {localFactor : Nat.Primes → ℂ}
    (hlocal :
      Summable (fun p : Nat.Primes => ‖localFactor p - 1‖)) :
    Summable (unrestrictedPrimeSupportTerm localFactor) := by
  change Summable
    (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, (localFactor p - 1))
  exact
    summable_finsetProd_of_summable_norm
      (f := fun p : Nat.Primes => localFactor p - 1)
      hlocal





/-! ## Absolute convergence of paired-Fourier local errors -/











/-! ## Direct-good-prime and carry-block versions -/





namespace SelectedCFZCarryFourierBlockData











end SelectedCFZCarryFourierBlockData

/-! ## Exact paired-Fourier specialization -/





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

theorem
    summable_norm_cfzCanonicalCarryPairedFourierPrimeLocalFactor_sub_one
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b R : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ) (t u : κ → ℝ)
    (hnonzero :
      NonzeroCoefficientVectors
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hindependent :
      PairwiseIndependentCoefficients
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hR : 2 ≤ R) :
    Summable (fun p : Nat.Primes =>
      ‖cfzCanonicalCarryPairedFourierPrimeLocalFactor
          N W b R forms carry t u p - 1‖) := by
  simpa only [cfzCanonicalCarryPairedFourierPrimeLocalFactor] using
    summable_norm_pairedFourierPrimeLocalFactor_sub_one
      hnonzero hindependent hR t u







/-! ## Coordinatewise support-fiber bounds -/























/-! ## The named carry-weighted truncation majorant -/









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

/-- A selected canonical carry family has no zero coefficient vector after
primorial scaling.  The carry and the reduced-residue representative occur
only in the affine constants. -/
theorem selectedCFZCarryAdjustedFamilyAtVector_nonzero
    {k N w b : ℕ}
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ) :
    NonzeroCoefficientVectors
      (cfzCarryAdjustedFamilyAtVector
        N (primorial w) b
        (fun q : SelectedCFZFormIndex e => q.1) carry) := by
  intro q hzero
  apply cfzCoefficient_ne_zero hk q.1
  funext v
  have hv := congrFun hzero v
  simp only [cfzCarryAdjustedFamilyAtVector,
    cfzCarryAdjustedAffineForm_coefficient] at hv
  have hW : ((primorial w : ℕ) : ℤ) ≠ 0 := by
    exact_mod_cast (primorial_pos w).ne'
  exact (mul_eq_zero.mp hv).resolve_left hW



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

/-- At every fixed frequency, the complete support series for a selected
canonical carry is absolutely convergent.  This packages the coefficient
geometry established at the start of the file into the generic unrestricted
support summability theorem. -/
theorem summable_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ) :
    Summable (fun S : Finset Nat.Primes =>
      unrestrictedPrimeSupportTerm
        (cfzCanonicalCarryPairedFourierPrimeLocalFactor
          N (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          carry t u) S) := by
  exact
    summable_unrestrictedPrimeSupportTerm
      (summable_norm_cfzCanonicalCarryPairedFourierPrimeLocalFactor_sub_one
        N (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1)
        carry t u
        (selectedCFZCarryAdjustedFamilyAtVector_nonzero hk e carry)
        (selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
          hk e carry)
        hR)



















/-! ## Exact remaining interface for diagonal growing-box decay -/

















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

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- For one carry cell, the completed support series times the paired
Fourier envelope is bounded by the full complete-support mass. -/
theorem
    solution
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (hbound :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) ≤ w)
    (hwb : (primorial w).Coprime b)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
        cfzCanonicalCarryCompletePrimeSupportSeries
          N (primorial w) b R
          (fun q : SelectedCFZFormIndex e => q.1)
          carry tu.1 tu.2‖ ≤
      selectedCFZCanonicalCompleteSupportMass e R *
        χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
  have hseries :=
    summable_selectedCFZCanonicalCarry_unrestrictedPrimeSupportTerm
      (N := N) (w := w) (b := b)
      hk e carry hR tu.1 tu.2
  have hintegrand :=
    hseries.mul_left
      (pairedCutoffFourierEnvelope χ tu.1 tu.2)
  have hmajorant :
      Summable (fun S : Finset Nat.Primes =>
        selectedCFZCanonicalCompleteSupportMajorant e R S *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu) :=
    (summable_selectedCFZCanonicalCompleteSupportMajorant e hR).mul_right
      (χ.selectedCFZPairedFourierAbsoluteDensity e tu)
  unfold cfzCanonicalCarryCompletePrimeSupportSeries
  rw [← tsum_mul_left]
  calc
    ‖∑' S : Finset Nat.Primes,
        pairedCutoffFourierEnvelope χ tu.1 tu.2 *
          unrestrictedPrimeSupportTerm
            (cfzCanonicalCarryPairedFourierPrimeLocalFactor
              N (primorial w) b R
              (fun q : SelectedCFZFormIndex e => q.1)
              carry tu.1 tu.2) S‖ ≤
        ∑' S : Finset Nat.Primes,
          ‖pairedCutoffFourierEnvelope χ tu.1 tu.2 *
            unrestrictedPrimeSupportTerm
              (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                N (primorial w) b R
                (fun q : SelectedCFZFormIndex e => q.1)
                carry tu.1 tu.2) S‖ :=
      norm_tsum_le_tsum_norm hintegrand.norm
    _ ≤
        ∑' S : Finset Nat.Primes,
          selectedCFZCanonicalCompleteSupportMajorant e R S *
            χ.selectedCFZPairedFourierAbsoluteDensity e tu :=
      hintegrand.norm.tsum_le_tsum
        (fun S =>
          χ.norm_selectedCFZCanonicalCarryCompleteSupportIntegrand_le
            (N := N) hk hbound hwb e carry hR S tu)
        hmajorant
    _ =
        selectedCFZCanonicalCompleteSupportMass e R *
          χ.selectedCFZPairedFourierAbsoluteDensity e tu := by
      rw [tsum_mul_right]
      rfl
