-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy_eq_tsum_tail
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:58:28.703108+00:00
-- url     : https://prove2.me/submissions/45118525-dfff-467f-ab38-ed159eeeb30d

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_pairedEnvelope_mul_selectedCFZCanonicalCarry_finite_sub_complete_eq_tail
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_summable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

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
/-! ## A summable uniform majorant and `L¹` convergence -/
/-! ## The completion tail as one absolutely convergent series -/

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- The complete canonical Euler discrepancy is pointwise the single
signed tail series indexed above. -/
theorem solution
    {k N w b : ℕ} [NeZero N]
    (χ : SmoothSieveCutoff)
    (hk : 2 ≤ k)
    (e : LinearFormsExponent k)
    {R : ℕ} (hR : 2 ≤ R)
    (tu :
      (SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) :
    χ.cfzCanonicalCarryEulerCompletionDiscrepancy
        (N := N) (primorial w) b R
        (fun q : SelectedCFZFormIndex e => q.1) tu =
      ∑' idx :
          SelectedCFZCanonicalCarryEulerCompletionTailIndex e R,
        χ.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
          (N := N) (w := w) (b := b) e R idx tu := by
  classical
  have htail :=
    χ.summable_selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      (N := N) (w := w) (b := b) hk e hR tu
  unfold SmoothSieveCutoff.cfzCanonicalCarryEulerCompletionDiscrepancy
    SmoothSieveCutoff.cfzCanonicalCarryCompleteEulerIntegrand
    cfzCanonicalCarryUnrestrictedFourierAverage
    cfzCanonicalCarryCompleteFourierAverage
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc
    ∑ carry ∈ cfzCanonicalCarryVectorChoices
          (SelectedCFZFormIndex e) k,
        (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              ((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                ∑ S ∈ (primesLEAsPrimes R).powerset,
                  unrestrictedPrimeSupportTerm
                    (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                      N (primorial w) b R
                      (fun q : SelectedCFZFormIndex e => q.1)
                      carry tu.1 tu.2) S) -
            pairedCutoffFourierEnvelope χ tu.1 tu.2 *
              ((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
                cfzCanonicalCarryCompletePrimeSupportSeries
                  N (primorial w) b R
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry tu.1 tu.2)) =
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k,
          ∑' S :
              ↥((↑((primesLEAsPrimes R).powerset) :
                Set (Finset Nat.Primes))ᶜ),
            -((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) S.1)) := by
      apply Finset.sum_congr rfl
      intro carry hcarry
      have hcompletion :=
        χ.pairedEnvelope_mul_selectedCFZCanonicalCarry_finite_sub_complete_eq_tail
          (N := N) (w := w) (b := b)
          hk e carry hR tu.1 tu.2
      rw [show
          pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                ((cfzCanonicalCarryCellDensity
                    (N := N)
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry : ℂ) *
                  ∑ S ∈ (primesLEAsPrimes R).powerset,
                    unrestrictedPrimeSupportTerm
                      (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                        N (primorial w) b R
                        (fun q : SelectedCFZFormIndex e => q.1)
                        carry tu.1 tu.2) S) -
              pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                ((cfzCanonicalCarryCellDensity
                    (N := N)
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry : ℂ) *
                  cfzCanonicalCarryCompletePrimeSupportSeries
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) =
            (cfzCanonicalCarryCellDensity
                (N := N)
                (fun q : SelectedCFZFormIndex e => q.1)
                carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                    (∑ S ∈ (primesLEAsPrimes R).powerset,
                      unrestrictedPrimeSupportTerm
                        (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                          N (primorial w) b R
                          (fun q : SelectedCFZFormIndex e => q.1)
                          carry tu.1 tu.2) S) -
                pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                  cfzCanonicalCarryCompletePrimeSupportSeries
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) by ring,
        hcompletion]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro S
      ring
    _ = _ := by
      unfold
        SelectedCFZCanonicalCarryEulerCompletionTailIndex at htail ⊢
      rw [htail.tsum_prod]
      unfold
        SmoothSieveCutoff.selectedCFZCanonicalCarryEulerCompletionTailIntegrand
      let F : (SelectedCFZFormIndex e → ℤ) → ℂ :=
        fun carry =>
          ∑' S :
              ↥((↑((primesLEAsPrimes R).powerset) :
                Set (Finset Nat.Primes))ᶜ),
            -((cfzCanonicalCarryCellDensity
                  (N := N)
                  (fun q : SelectedCFZFormIndex e => q.1)
                  carry : ℂ) *
              (pairedCutoffFourierEnvelope χ tu.1 tu.2 *
                unrestrictedPrimeSupportTerm
                  (cfzCanonicalCarryPairedFourierPrimeLocalFactor
                    N (primorial w) b R
                    (fun q : SelectedCFZFormIndex e => q.1)
                    carry tu.1 tu.2) S.1))
      change
        ∑ carry ∈ cfzCanonicalCarryVectorChoices
              (SelectedCFZFormIndex e) k,
            F carry =
          ∑' carry :
              ↥(cfzCanonicalCarryVectorChoices
                (SelectedCFZFormIndex e) k),
            F carry.1
      exact
        (Finset.tsum_subtype
          (cfzCanonicalCarryVectorChoices
            (SelectedCFZFormIndex e) k) F).symm
