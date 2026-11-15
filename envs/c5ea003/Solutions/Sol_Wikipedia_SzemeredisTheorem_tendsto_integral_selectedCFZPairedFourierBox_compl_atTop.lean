-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_integral_selectedCFZPairedFourierBox_compl_atTop
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:48:42.310263+00:00
-- url     : https://prove2.me/submissions/5a67fa71-f297-4179-af68-8d621e6647e9

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryBoundaryBound
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryCellPartition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCarryEulerBridge
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CFZCanonicalCompleteMainTermBridge
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
# Fourier inversion with the CFZ carry-block average retained

The carry decomposition does not produce one common arithmetic Euler
product.  For a paired divisor family `z`, both the quotient-block box and
the local prime product depend on `pairedDivisorLcm z`.  This file keeps
that dependence inside the finite divisor sum and applies Fourier inversion
only to the smooth coefficient of each individual family.

Thus the exact integrand below has the honest shape

`∑ z, (mean over the quotient blocks belonging to z) *
  (transformed coefficient belonging to z)`.

No multiplicative closure of the truncated choices `d ≤ R` is used.  The
last results also split the exact integral into a finite Fourier box and its
complement, providing the interface needed for a subsequent uniform
Fourier-box comparison and tail estimate.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff

/-! ## The blockwise arithmetic coefficient -/







/-! ## The carry-dependent Fourier integrand -/









/-! ## Exact divisor-sum and scaled-main-term bridges -/





/-! ## Exact finite-box decomposition -/



theorem measurableSet_selectedCFZPairedFourierBox
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    MeasurableSet (selectedCFZPairedFourierBox e T) := by
  unfold selectedCFZPairedFourierBox fourierProductBox
  exact
    Metric.isClosed_closedBall.measurableSet.prod
      Metric.isClosed_closedBall.measurableSet





end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Honest Fourier-tail bounds for the carry-block divisor expansion

The carry-block Fourier integrand is a finite sum indexed by paired divisor
families.  Taking absolute values before summing loses the cancellation that
will eventually come from the arithmetic Euler product.  This file records
the sharp domination available without making such a cancellation claim.

The loss is isolated in `selectedCFZCarryFourierCoefficientMass`.  Unlike the
raw cardinality `R ^ (2m)`, this quantity retains both the carry-block Euler
coefficient and every Möbius zero.  The remaining analytic factor is a
genuine Schwartz tail, independent of `R`, `W`, `b`, and the divisor family.

Consequently the fully Selberg-scaled complementary integral tends to zero
as soon as the correspondingly scaled coefficient mass is eventually
bounded.  After exceptional-prime coverage, the coefficient mass is further
reduced to a harmonic LCM mass.  The remaining finite combinatorial estimate
is the expected prime-support bound

`harmonicLcmMass R ≤ ∏ p ∈ primesLE R,
  (1 + (2 ^ (2 * m) - 1) / p)`.

Together with the standard zeta-at-`1 + 1 / log R` majorization this is
polylogarithmic, and an arbitrarily high Schwartz moment then beats it at
`T = sqrt (log R)`.  That prime-support estimate is made explicit as the
sole missing step; it is not replaced by the useless raw divisor-choice
count.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius BigOperators Topology

namespace SmoothSieveCutoff

/-! ## The exact coefficient mass retained by triangle domination -/









/-! ## Elementary bounds for the retained arithmetic coefficients -/













/-! ## Harmonic LCM gain when `W` covers the exceptional primes -/























/-! ## The universal paired Schwartz density -/











/-- The product of the two coordinatewise sup-norm boxes is exactly the
closed ball for the product sup norm. -/
theorem selectedCFZPairedFourierBox_eq_closedBall
    {k : ℕ} (e : LinearFormsExponent k) (T : ℝ) :
    selectedCFZPairedFourierBox e T =
      Metric.closedBall
        (0 :
          (SelectedCFZFormIndex e → ℝ) ×
            (SelectedCFZFormIndex e → ℝ))
        T := by
  ext tu
  simp [selectedCFZPairedFourierBox, fourierProductBox,
    Metric.mem_closedBall, Prod.norm_def]





/-! ## Pointwise transform domination -/









/-! ## Complementary-integral and scaled bounds -/





/-! ## The exact remaining arithmetic hypothesis -/

























end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# Canonical complete-Euler main-term bridge

This file joins the two exact full-space cancellations in the canonical
CFZ expansion.

* Coordinatewise divisor truncation has zero full-space Fourier integral.
* Completing the finite prime support to the honest Euler support has zero
  full-space Fourier integral in the primorial exceptional-prime regime.

Consequently the canonical cyclic-boundary main term is exactly the
Selberg-scaled full-space integral of the complete Euler integrand.

The second half separates this integral into the standard growing Fourier
box and its complement.  The completed complement is already uniformly
controlled by `CFZCanonicalEulerCompletionTail`; the sole remaining input
is an interior pointwise comparison with the normalized archimedean
baseline.
-/
open Wikipedia.SzemeredisTheorem
open Filter MeasureTheory Topology
open scoped BigOperators
/-! ## Integrability of the complete canonical Euler model -/
/-! ## Exact finite-to-complete main term -/
/-! ## Scaled integrand and normalized archimedean baseline -/

open Wikipedia.SzemeredisTheorem in
/-- The integral of any fixed integrable function over the complement of
the selected paired Fourier box tends to zero. -/
theorem solution
    {k : ℕ} (e : LinearFormsExponent k)
    {f :
      ((SelectedCFZFormIndex e → ℝ) ×
        (SelectedCFZFormIndex e → ℝ)) → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    Tendsto
      (fun T : ℝ =>
        ∫ tu in
            (SmoothSieveCutoff.selectedCFZPairedFourierBox e T)ᶜ,
          f tu ∂(volume.prod volume))
      atTop (𝓝 0) := by
  have hcover :
      AECover (volume.prod volume) atTop
        (fun T : ℝ =>
          SmoothSieveCutoff.selectedCFZPairedFourierBox e T) := by
    have hclosed :
        AECover (volume.prod volume) atTop
          (fun T : ℝ =>
            Metric.closedBall
              (0 :
                (SelectedCFZFormIndex e → ℝ) ×
                  (SelectedCFZFormIndex e → ℝ))
              T) :=
      aecover_closedBall tendsto_id
    convert hclosed using 1
    funext T
    exact
      SmoothSieveCutoff.selectedCFZPairedFourierBox_eq_closedBall e T
  have hinside :
      Tendsto
        (fun T : ℝ =>
          ∫ tu in
              SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
            f tu ∂(volume.prod volume))
        atTop
        (𝓝 (∫ tu, f tu ∂(volume.prod volume))) :=
    hcover.integral_tendsto_of_countably_generated hf
  have hconst :
      Tendsto
        (fun _ : ℝ =>
          ∫ tu, f tu ∂(volume.prod volume))
        atTop
        (𝓝 (∫ tu, f tu ∂(volume.prod volume))) :=
    tendsto_const_nhds
  have hsub :
      Tendsto
        (fun T : ℝ =>
          (∫ tu, f tu ∂(volume.prod volume)) -
            ∫ tu in
                SmoothSieveCutoff.selectedCFZPairedFourierBox e T,
              f tu ∂(volume.prod volume))
        atTop (𝓝 0) := by
    convert hconst.sub hinside using 1
    all_goals simp
  refine hsub.congr' (Filter.Eventually.of_forall fun T => ?_)
  symm
  exact
    setIntegral_compl
      (SmoothSieveCutoff.measurableSet_selectedCFZPairedFourierBox e T)
      hf
