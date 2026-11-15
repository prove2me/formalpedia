-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.smallPrimeZetaCorrection_mul_selectedCFZCanonicalCarryLargePrimeEulerCorrection
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T12:03:05.867195+00:00
-- url     : https://prove2.me/submissions/d52528a4-a0b6-4730-84a9-17ae7b6cff66

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_mem_smallPrimeFinset
import Theorems.Thm_Wikipedia_SzemeredisTheorem_multipliable_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_smallPrime_compl
import Theorems.Thm_Wikipedia_SzemeredisTheorem_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_eq_inv_of_small

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

section



/-!
# Exact small/large-prime factorization on CFZ carry blocks

The carry constants introduced by quotient-block decomposition do not
disturb the W-trick at primes dividing `W`: every carry-adjusted affine form
is still the constant reduced residue `b` modulo such a prime.  This file
upgrades that observation from real avoidance products to the complex
Fourier local factors.

For a packaged selected carry block we consequently identify the product of
the arithmetic/zeta ratios at `p ≤ w` with the already normalized
`smallPrimeZetaCorrection`.  The complementary product is exactly the
bounded-mask product from `CFZCarryEulerTail`.  Once `w` contains the
fixed `k`-exceptional range, the direct `O_k(p⁻²)` estimate proves
multipliability on the complement and yields an exact small/large split of
the complete arithmetic correction.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Unit complex factors at primes dividing the primorial -/







/-! ## Exact small-prime correction for a packaged carry block -/







/-! ## The complementary product and the exact complete correction -/

/-- Masking primes at most `w` is the multiplicative indicator of the
set-theoretic complement of `smallPrimeFinset w`. -/
theorem boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator
    (w : ℕ) (localFactor : Nat.Primes → ℂ) :
    boundedMaskedComplexPrimeLocalFactor w localFactor =
      ((smallPrimeFinset w : Set Nat.Primes)ᶜ).mulIndicator
        localFactor := by
  funext p
  by_cases hp : (p : ℕ) ≤ w
  · have hmem : p ∈ smallPrimeFinset w :=
      mem_smallPrimeFinset.mpr hp
    simp [boundedMaskedComplexPrimeLocalFactor, hp, hmem]
  · have hnotmem : p ∉ smallPrimeFinset w := by
      simpa [mem_smallPrimeFinset] using hp
    simp [boundedMaskedComplexPrimeLocalFactor, hp, hnotmem]







end Wikipedia.SzemeredisTheorem

end

section



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

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped BigOperators

/-! ## Packaged canonical carry-vector data -/



namespace SelectedCFZCanonicalCarryFourierData









end SelectedCFZCanonicalCarryFourierData

/-! ## Direct good-prime geometry -/



/-! ## Uniform prime-square control and Euler tail -/







/-! ## Exact small/large-prime factorization -/







/-- The finite product over `p ≤ w` is the standard small-prime
correction. -/
theorem prod_selectedCFZCanonicalCarrySmallPrimeArithmeticToZetaRatio_eq
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k)
    (hwb : (primorial d.w).Coprime d.b) :
    ∏ p ∈ smallPrimeFinset d.w,
        d.primeArithmeticToZetaLocalRatio p =
      smallPrimeZetaCorrection d.R d.w d.t d.u := by
  apply Finset.prod_congr rfl
  intro p hp
  exact
    selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_eq_inv_of_small
      d hwb hp

/-- The bounded mask is exactly the unordered product on the complement
of the small-prime finset. -/
theorem
    selectedCFZCanonicalCarryLargePrimeEulerCorrection_eq_tprod_smallPrime_compl
    {k : ℕ} (d : SelectedCFZCanonicalCarryFourierData k) :
    d.largePrimeEulerCorrection =
      ∏' p :
          ↑((smallPrimeFinset d.w : Set Nat.Primes)ᶜ),
        d.primeArithmeticToZetaLocalRatio p := by
  rw [
    SelectedCFZCanonicalCarryFourierData.largePrimeEulerCorrection,
    tprod_subtype,
    ←
      boundedMaskedComplexPrimeLocalFactor_eq_smallPrime_compl_mulIndicator]





/-! ## Exact normalized completed-Euler identities -/





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

open Wikipedia.SzemeredisTheorem in
/-- Exact small/large factorization of the complete arithmetic
correction for one canonical carry vector. -/
theorem
    solution
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R)
    (hw :
      wTrickedCFZComplexExceptionalBound k ≤ d.w)
    (hwb : (primorial d.w).Coprime d.b) :
    smallPrimeZetaCorrection d.R d.w d.t d.u *
        d.largePrimeEulerCorrection =
      ∏' p : Nat.Primes,
        d.primeArithmeticToZetaLocalRatio p := by
  rw [←
      prod_selectedCFZCanonicalCarrySmallPrimeArithmeticToZetaRatio_eq
        d hwb,
    selectedCFZCanonicalCarryLargePrimeEulerCorrection_eq_tprod_smallPrime_compl]
  rw [←
    Finset.tprod_subtype'
      (smallPrimeFinset d.w)
      d.primeArithmeticToZetaLocalRatio]
  exact
    Multipliable.tprod_mul_tprod_compl
      ((smallPrimeFinset d.w).multipliable
        d.primeArithmeticToZetaLocalRatio)
      (multipliable_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_smallPrime_compl
        hk d hR hw)
