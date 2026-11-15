-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.tendsto_selectedCFZCanonicalCarryLargePrimeEulerCorrection_one
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:01:46.065785+00:00
-- url     : https://prove2.me/submissions/1a2d2d46-d005-4daf-b946-bdbc87131b28

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_HasComplexPrimeSquareError_tendsto_tprod_one
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_sub_one_le

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
# Complex good-prime local factors after Fourier inversion

Fourier inversion turns each of the two smooth divisor sums attached to a
form into a complex multiplicative phase.  At a prime `p`, if the two phases
are `z` and `w`, the four squarefree divisor choices contribute

`1 - (z + w - z * w) 1_{p ∣ ψ(x)}`.

Thus the arithmetic local factor is a complex-weighted avoidance average.
This file develops that average directly over `ℂ`, proves its exact finite
inclusion--exclusion expansion, and isolates the singleton contribution.
At a rank-two good prime the remaining supports have density at most
`p⁻²`, so the complex remainder is bounded by the product of
`1 + ‖a q‖`.

For the Fourier coefficients, every divisor phase has norm at most one when
`R ≥ 2`, hence `‖z + w - z * w‖ ≤ 3`.  Consequently the higher-order
coefficient mass is at most `4 ^ m` for a system of `m` forms.  Above
`p ≥ 6m`, the complex first-order model has norm at least `1/2`; division by
that model therefore gives the explicit ratio estimate

`‖localRatio p - 1‖ ≤ 2 * 4 ^ m / p²`.

The final CFZ theorem masks the finite exceptional range and packages these
ratios in a complex analogue of `HasPrimeSquareError`, including
multipliability of the resulting remainder Euler product.

This does not yet compare the first-order model with the local factors of
the appropriate multivariate zeta quotient.  That analytic comparison, and
the subsequent parameter-uniform integration, are separate steps.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Complex finite averages -/









/-! ## Exact complex inclusion--exclusion -/















/-! ## Norm bounds for the complex remainder -/













/-! ## A stable complex first-order ratio -/









/-! ## Fourier phase coefficients -/

namespace SmoothSieveCutoff





end SmoothSieveCutoff

























/-! ## Complex square-error Euler-product interface -/



namespace HasComplexPrimeSquareError











end HasComplexPrimeSquareError



@[simp]
theorem boundedMaskedComplexPrimeLocalFactor_of_le
    {B : ℕ} {localFactor : Nat.Primes → ℂ}
    {p : Nat.Primes} (hp : (p : ℕ) ≤ B) :
    boundedMaskedComplexPrimeLocalFactor B localFactor p = 1 := by
  simp [boundedMaskedComplexPrimeLocalFactor, hp]

@[simp]
theorem boundedMaskedComplexPrimeLocalFactor_of_lt
    {B : ℕ} {localFactor : Nat.Primes → ℂ}
    {p : Nat.Primes} (hp : B < (p : ℕ)) :
    boundedMaskedComplexPrimeLocalFactor B localFactor p =
      localFactor p := by
  have hnot : ¬(p : ℕ) ≤ B :=
    Nat.not_le.mpr hp
  simp [boundedMaskedComplexPrimeLocalFactor, hnot]

/-- A complex square-error estimate above a cutoff becomes global after
masking. -/
theorem hasComplexPrimeSquareError_boundedMasked
    {C : ℝ} {localFactor : Nat.Primes → ℂ}
    (B : ℕ) (hC : 0 ≤ C)
    (herror :
      ∀ p : Nat.Primes, B < (p : ℕ) →
        ‖localFactor p - 1‖ ≤ C / (p : ℝ) ^ 2) :
    HasComplexPrimeSquareError C
      (boundedMaskedComplexPrimeLocalFactor B localFactor) := by
  refine ⟨hC, fun p => ?_⟩
  by_cases hp : (p : ℕ) ≤ B
  · rw [boundedMaskedComplexPrimeLocalFactor_of_le hp]
    simp only [sub_self, norm_zero]
    exact div_nonneg hC (sq_nonneg (p : ℝ))
  · have hlt : B < (p : ℕ) :=
      Nat.lt_of_not_ge hp
    rw [boundedMaskedComplexPrimeLocalFactor_of_lt hlt]
    exact herror p hlt

/-! ## CFZ specialization -/















end Wikipedia.SzemeredisTheorem

end

section



/-!
# Uniform tails of complex Euler products

The local estimates used in the smooth sieve are uniform in the Fourier
variables but the local-factor family itself changes with all asymptotic
parameters.  Ordinary convergence of one fixed Euler product is therefore
not enough.

This file packages the required dominated-convergence statement.  If a
varying family has the common bound

`‖L_n(p) - 1‖ ≤ C / p²`

and each fixed prime factor tends to one, then the full unordered products
also tend to one.  A second theorem specializes this to the standard
large-prime mask: all factors at `p ≤ w_n` are replaced by one, and
`w_n → ∞`.  No bound on the Fourier variables is needed because the local
square-error estimate is already uniform in them.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

namespace HasComplexPrimeSquareError



end HasComplexPrimeSquareError

/-- Once a numerical cutoff tends to infinity, the factor at each fixed
prime in the corresponding bounded mask is eventually exactly one. -/
theorem tendsto_boundedMaskedComplexPrimeLocalFactor_one
    {α : Type*} {𝓕 : Filter α}
    (w : α → ℕ)
    (localFactor : α → Nat.Primes → ℂ)
    (hw : Tendsto w 𝓕 atTop)
    (p : Nat.Primes) :
    Tendsto
      (fun n =>
        boundedMaskedComplexPrimeLocalFactor
          (w n) (localFactor n) p)
  𝓕 (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [hw (eventually_ge_atTop (p : ℕ))]
    with n hn
  exact
    (boundedMaskedComplexPrimeLocalFactor_of_le hn).symm

/-- **Uniform large-prime Euler-tail theorem.**  The unmasked local family
may vary arbitrarily with `n`.  It is enough to have one common
`O(p⁻²)` estimate beyond the varying cutoff `w n`. -/
theorem tendsto_tprod_boundedMaskedComplexPrimeLocalFactor_one
    {α : Type*} {𝓕 : Filter α}
    {C : ℝ} (hC : 0 ≤ C)
    (w : α → ℕ)
    (localFactor : α → Nat.Primes → ℂ)
    (hw : Tendsto w 𝓕 atTop)
    (herror :
      ∀ᶠ n in 𝓕, ∀ p : Nat.Primes,
        w n < (p : ℕ) →
          ‖localFactor n p - 1‖ ≤
            C / (p : ℝ) ^ 2) :
    Tendsto
      (fun n =>
        ∏' p : Nat.Primes,
          boundedMaskedComplexPrimeLocalFactor
            (w n) (localFactor n) p)
      𝓕 (𝓝 1) := by
  apply
    HasComplexPrimeSquareError.tendsto_tprod_one
  · filter_upwards [herror] with n hn
    exact
      hasComplexPrimeSquareError_boundedMasked
        (w n) hC (fun p hp => hn p hp)
  · exact fun p =>
      tendsto_boundedMaskedComplexPrimeLocalFactor_one
        w localFactor hw p

end Wikipedia.SzemeredisTheorem

end

section



/-!
# Comparing Fourier local factors with zeta Euler models

For one pair of Fourier phases `z, w` and `r = 1 / p`, the first-order
arithmetic model is

`1 - r * (z + w - z * w)`.

The corresponding local factor of the zeta quotient is

`((1 - r * z) * (1 - r * w)) / (1 - r * z * w)`.

Their difference has the exact factorization

`r² z w (1 - z) (1 - w) / (1 - r z w)`.

At a prime, the Fourier phases have norm at most one.  The denominator is
therefore bounded below by `1/2`, and the difference is at most `8 / p²`,
uniformly in both Fourier parameters.

For a finite system of `m` forms, expanding the product separates the sum
of the singleton errors from supports of size at least two.  Above `p ≥ 7`,
the latter are bounded by `49 * 2^m / p²`.  This gives an explicit
finite-system comparison with the combined first-order model, and hence a
ratio comparison above the additional stability cutoff `p ≥ 6m`.

The final section combines this result with the affine rank-two calculation
from `ComplexLocalFactorControl`.  It remains entirely local: no infinite
prime-product identity and no multivariate Fourier integration is asserted.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## A generic finite-product second-order remainder -/









/-! ## One paired phase -/















/-! ## Exact cpow coordinates -/













/-! ## Finite systems -/



























/-! ## Direct arithmetic/zeta comparison -/



















theorem complexArithmeticZetaRatioErrorConstant_nonneg
    (m : ℕ) :
    0 ≤ complexArithmeticZetaRatioErrorConstant m := by
  rw [complexArithmeticZetaRatioErrorConstant,
    complexArithmeticZetaDifferenceConstant,
    complexZetaModelDifferenceConstant]
  positivity



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
# Uniform Euler tails on CFZ carry blocks

The carry-block reduction leaves a genuinely varying affine system.  The
paired divisor choice determines the block side length, the point of the
quotient block determines all carry constants, and all of these data may
vary with the asymptotic parameter.  This file keeps that dependence.

At a prime outside the primorial, carry corrections alter only affine
constants.  The direct modular one-form and rank-two predicates therefore
give the same `O_k(p⁻²)` arithmetic-to-zeta ratio estimate on every block,
uniformly in the divisor choice and in both Fourier variables.  The general
dominated Euler-product theorem then shows that the product over `p > w`
tends to one as `w → ∞`.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## A dependent package for a varying carry block -/



namespace SelectedCFZCarryFourierBlockData







end SelectedCFZCarryFourierBlockData

/-! ## Direct modular local estimate -/





/-! ## A `k`-only bound for every selected block -/



theorem selectedCFZCarryEulerTailErrorConstant_nonneg
    (k : ℕ) :
    0 ≤ selectedCFZCarryEulerTailErrorConstant k := by
  exact complexArithmeticZetaRatioErrorConstant_nonneg _







/-! ## Uniform large-prime tail -/



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

open Wikipedia.SzemeredisTheorem in
/-- The masked large-prime correction tends to one uniformly while every
datum other than the ambient `k` is allowed to vary. -/
theorem solution
    {α : Type*} {𝓕 : Filter α} {k : ℕ}
    (hk : 2 ≤ k)
    (d : α → SelectedCFZCanonicalCarryFourierData k)
    (hw : Tendsto (fun n => (d n).w) 𝓕 atTop)
    (hR : ∀ᶠ n in 𝓕, 2 ≤ (d n).R) :
    Tendsto
      (fun n => (d n).largePrimeEulerCorrection)
      𝓕 (𝓝 1) := by
  apply
    tendsto_tprod_boundedMaskedComplexPrimeLocalFactor_one
      (selectedCFZCarryEulerTailErrorConstant_nonneg k)
      (fun n => (d n).w)
      (fun n => (d n).primeArithmeticToZetaLocalRatio)
      hw
  filter_upwards
      [hR,
        hw
          (eventually_ge_atTop
            (wTrickedCFZComplexExceptionalBound k))]
    with n hnR hnlarge
  intro p hp
  have hpW : ¬(p : ℕ) ∣ primorial (d n).w := by
    rw [p.prop.dvd_primorial_iff]
    exact Nat.not_le.mpr hp
  exact
    norm_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
      hk (d n) hnR p hpW (hnlarge.trans_lt hp)
