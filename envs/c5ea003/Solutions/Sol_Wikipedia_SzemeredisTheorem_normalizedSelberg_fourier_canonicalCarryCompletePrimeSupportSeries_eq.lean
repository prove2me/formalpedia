-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.normalizedSelberg_fourier_canonicalCarryCompletePrimeSupportSeries_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:07:13.32472+00:00
-- url     : https://prove2.me/submissions/c23597d3-2e9f-4d79-802b-0b282de8546d

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryFourierNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCyclicBoundaryLimit
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierEulerNormalization
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryFourierTailPolylog
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCarryHarmonicLcmEulerBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCongruenceBoundary
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexEulerProductComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexLocalFactorControl
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ComplexZetaModelComparison
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
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
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_WTrickedEulerCorrectionLimit
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
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecificLimits.Basic
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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_normalizedSelberg_fourier_completeCanonicalCarryEuler_eq
import Theorems.Thm_Wikipedia_SzemeredisTheorem_selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
import Theorems.Thm_Wikipedia_SzemeredisTheorem_tsum_unrestrictedPairedFourierPrimeSupportTerm_eq

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





/-- The full fixed-carry support series is the already identified paired
Fourier Euler product. -/
theorem tsum_cfzCanonicalCarry_unrestrictedPrimeSupport_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {k : ℕ}
    (N W b : ℕ) (forms : κ → CFZFormIndex k)
    (carry : κ → ℤ)
    (hnonzero :
      NonzeroCoefficientVectors
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    (hindependent :
      PairwiseIndependentCoefficients
        (cfzCarryAdjustedFamilyAtVector N W b forms carry))
    {R : ℕ} (hR : 2 ≤ R) (t u : κ → ℝ) :
    (∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm
          (cfzCanonicalCarryPairedFourierPrimeLocalFactor
            N W b R forms carry t u) S) =
      (cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R
            (cfzCarryAdjustedFamilyAtVector N W b forms carry)
            t u p := by
  change
    (∑' S : Finset Nat.Primes,
        unrestrictedPrimeSupportTerm
          (pairedFourierPrimeLocalFactor R
            (cfzCarryAdjustedFamilyAtVector N W b forms carry)
            t u) S) = _
  simpa only [unrestrictedPairedFourierPrimeSupportTerm] using
    tsum_unrestrictedPairedFourierPrimeSupportTerm_eq
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









/-- Exact complete Euler identification for one selected canonical carry
vector in the primorial regime.  All coefficient-geometry hypotheses have
been discharged. -/
theorem tsum_selectedCFZCanonicalCarry_unrestrictedPrimeSupport_eq
    {k N w b : ℕ} [NeZero N]
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    (carry : SelectedCFZFormIndex e → ℤ)
    {R : ℕ} (hR : 2 ≤ R)
    (t u : SelectedCFZFormIndex e → ℝ) :
    cfzCanonicalCarryCompletePrimeSupportSeries
        N (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) carry t u =
      (cutoffZetaSingularFactor R t u *
          cutoffZetaSystemFactor R t u) *
        ∏' p : Nat.Primes,
          primePairedFourierArithmeticToZetaLocalRatio
            R
            (cfzCarryAdjustedFamilyAtVector
              N (primorial w) b
              (fun q : SelectedCFZFormIndex e => q.1) carry)
            t u p := by
  unfold cfzCanonicalCarryCompletePrimeSupportSeries
  exact
    tsum_cfzCanonicalCarry_unrestrictedPrimeSupport_eq
      N (primorial w) b
      (fun q : SelectedCFZFormIndex e => q.1) carry
      (selectedCFZCarryAdjustedFamilyAtVector_nonzero hk e carry)
      (selectedCFZCarryAdjustedFamilyAtVector_pairwiseIndependent
        hk e carry)
      hR t u



/-! ## Expanding one active prime support into nonempty form supports -/











/-! ## A large active prime is killed by full-space Fourier inversion -/





/-! ## A summable uniform majorant and `L¹` convergence -/





















/-! ## The completion tail as one absolutely convergent series -/





















/-! ## Exact remaining interface for diagonal growing-box decay -/

















end Wikipedia.SzemeredisTheorem

end
/-!
# Fourier normalization for canonical CFZ carry vectors

The canonical divisor expansion freezes one complete integer carry vector,
rather than a divisor-dependent quotient block.  This file gives that
carry-vector model the same local-ratio, Euler-tail, factorization, and
normalized Fourier API as the older carry-block model.

All estimates are uniform in the carry vector.  In particular, no
realizability or positive-density hypothesis is imposed: vectors which do
not occur in a canonical carry cell satisfy the same pointwise arithmetic
statements.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
open scoped BigOperators
/-! ## Packaged canonical carry-vector data -/
/-! ## Direct good-prime geometry -/
/-! ## Uniform prime-square control and Euler tail -/
/-! ## Exact small/large-prime factorization -/
/-! ## Exact normalized completed-Euler identities -/

open Wikipedia.SzemeredisTheorem in
/-- The same identity rewritten all the way to the exact complete
prime-support series used by the canonical Euler completion. -/
theorem
    solution
    {k : ℕ} (hk : 2 ≤ k)
    (χ : SmoothSieveCutoff)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (pairedCutoffFourierEnvelope χ d.t d.u *
            d.completePrimeSupportSeries)) =
      ((χ.normalizer : ℂ)⁻¹) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        χ.cutoffNormalizerSeparatedProduct (d.t, d.u) *
        normalizedCompletedFourierEulerCorrection
          d.R d.w d.t d.u d.largePrimeEulerCorrection := by
  let : NeZero d.N := d.N_neZero
  have hseries :=
    tsum_selectedCFZCanonicalCarry_unrestrictedPrimeSupport_eq
      (N := d.N) (w := d.w) (b := d.b)
      hk d.e d.carry hR d.t d.u
  have hnormalized :=
    normalizedSelberg_fourier_completeCanonicalCarryEuler_eq
      hk χ d hR hw hwb
  unfold
    SelectedCFZCanonicalCarryFourierData.completePrimeSupportSeries
  rw [hseries]
  calc
    (normalizedSelbergScale χ.normalizer d.R
          (primorial d.w) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
        (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
            Fintype.card (SelectedCFZFormIndex d.e) *
          (pairedCutoffFourierEnvelope χ d.t d.u *
            ((cutoffZetaSingularFactor d.R d.t d.u *
                cutoffZetaSystemFactor d.R d.t d.u) *
              ∏' p : Nat.Primes,
                primePairedFourierArithmeticToZetaLocalRatio
                  d.R d.carryAdjustedFamily d.t d.u p))) =
      (normalizedSelbergScale χ.normalizer d.R
            (primorial d.w) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
          (((Real.log (d.R : ℝ) ^ 2 : ℝ) : ℂ) ^
              Fintype.card (SelectedCFZFormIndex d.e) *
            (χ.fourierProductTransform d.t *
              χ.fourierProductTransform d.u *
              cutoffZetaSingularFactor d.R d.t d.u)) *
          cutoffZetaSystemFactor d.R d.t d.u *
          (∏' p : Nat.Primes,
            d.primeArithmeticToZetaLocalRatio p) := by
        unfold pairedCutoffFourierEnvelope
          SmoothSieveCutoff.fourierProductTransform
          primePairedFourierArithmeticToZetaLocalRatio
          SelectedCFZCanonicalCarryFourierData.primeArithmeticToZetaLocalRatio
        ring
    _ = _ := hnormalized
