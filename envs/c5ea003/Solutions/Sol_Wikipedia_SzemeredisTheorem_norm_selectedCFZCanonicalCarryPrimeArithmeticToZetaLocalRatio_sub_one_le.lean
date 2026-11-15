-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.norm_selectedCFZCanonicalCarryPrimeArithmeticToZetaLocalRatio_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T11:59:51.440394+00:00
-- url     : https://prove2.me/submissions/8282710c-3e9e-4e44-9504-d5692262e192

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le_of_goodPrime
import Theorems.Thm_Wikipedia_SzemeredisTheorem_selectedCFZCarryAdjustedFamilyAtVector_goodPrime

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









theorem complexZetaModelDifferenceConstant_eq_natCast
    (m : ℕ) :
    complexZetaModelDifferenceConstant m =
      (complexZetaModelDifferenceNat m : ℝ) := by
  rw [complexZetaModelDifferenceConstant,
    complexZetaModelDifferenceNat]
  push_cast
  ring













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
# The complex arithmetic Euler product as zeta model times correction

`ComplexZetaModelComparison` proves, at every sufficiently large prime, that
the exact affine-system local factor divided by its zeta Euler model is
`1 + O_m(p⁻²)`.  This file promotes that local estimate to an unordered
Euler product.

There are three small points which are made explicit here.

* The exceptional cutoff contains both the finite affine-rank exceptional
  set and the quantitative nonvanishing range for the zeta model.
* The zeta model is in fact nonzero at every prime.  Consequently the
  arithmetic/zeta ratio is defined by honest cancellation at all primes.
* Replacing the finitely many uncontrolled ratios by one gives a globally
  square-decaying family.  The cutoff also makes every remaining ratio
  lie in the radius-`1/2` ball around one, so the masked family is
  pointwise nonzero.  Mathlib's finite-change theorem for products in a
  commutative group-with-zero then restores the exceptional factors.

Combining the resulting correction product with
`cutoffZetaEulerLocalFactor_hasProd` identifies the exact arithmetic prime
product as

`(elementary singular factor) * (completed zeta factor) *
  (convergent arithmetic correction)`.

No nonvanishing assertion is made for the correction without an explicit
nonvanishing hypothesis on the arithmetic local factors: a complex finite
average can in principle vanish.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators

/-! ## Prime-indexed local factors and the common cutoff -/



theorem complexArithmeticZetaRatioErrorConstant_eq_natCast
    (m : ℕ) :
    complexArithmeticZetaRatioErrorConstant m =
      (complexArithmeticZetaRatioErrorNat m : ℝ) := by
  rw [complexArithmeticZetaRatioErrorConstant,
    complexArithmeticZetaDifferenceConstant,
    complexZetaModelDifferenceConstant_eq_natCast,
    complexArithmeticZetaRatioErrorNat]
  push_cast
  ring











/-! ## Pointwise nonvanishing of the zeta model -/











/-! ## Square decay and the convergent correction product -/





















/-! ## Exact global Euler-product identification -/









end Wikipedia.SzemeredisTheorem

end

section




/-!
# Large-prime geometry for W-tricked affine systems

The integer exceptional-prime bound of a system scales with `W` after
replacing every form `ψ` by `W * ψ + b`.  That bound is therefore the wrong
interface for the large primes in the W-tricked Euler product.  Modulo a
prime `p ∤ W`, multiplication by `W` is a unit.  Consequently:

* a nonzero coefficient modulo `p` stays nonzero;
* every nonzero two-by-two coefficient minor stays nonzero, since the minor
  is multiplied by `W²`;
* affine constants play no role in either assertion and may vary from form
  to form.

This file packages that observation as direct modular good-prime predicates,
derives the exact one- and two-form densities without applying an exceptional
bound to the transformed integer system, and rebuilds the complex
paired-Fourier local-factor estimates from those modular hypotheses.

The final results apply uniformly to every subtype `SelectedCFZFormIndex e`.
Their exceptional cutoff depends only on the ambient CFZ parameter `k`.
The W-trick contributes only the natural hypothesis `p ∤ W`; neither the
size of `W` nor any (possibly carry-dependent) affine constant enters the
cutoff.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Modular one-form geometry -/









/-! ## Scaling identities and W-trick preservation -/

















/-! ## Exact one- and two-form densities -/









/-! ## Complex first-order expansion from modular geometry -/





/-! ## Stable complex and paired-Fourier ratios -/







/-! ## Direct comparison with the zeta Euler model -/





/-! ## Uniform selected-CFZ specialization -/

/-- The number of forms selected by a Boolean exponent is at most the
number of forms in the ambient CFZ system. -/
theorem card_selectedCFZFormIndex_le
    {k : ℕ} (e : LinearFormsExponent k) :
    Fintype.card (SelectedCFZFormIndex e) ≤
      Fintype.card (CFZFormIndex k) := by
  exact Fintype.card_subtype_le _

/-- The elementary zeta-model comparison cutoff is monotone in the number
of forms. -/
theorem complexZetaModelComparisonCutoff_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexZetaModelComparisonCutoff m ≤
      complexZetaModelComparisonCutoff n := by
  unfold complexZetaModelComparisonCutoff
  exact max_le_max le_rfl (Nat.mul_le_mul_left 6 hmn)

/-- The natural-valued zeta-model error constant is monotone in the number
of forms. -/
theorem complexZetaModelDifferenceNat_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexZetaModelDifferenceNat m ≤
      complexZetaModelDifferenceNat n := by
  unfold complexZetaModelDifferenceNat
  exact Nat.add_le_add
    (Nat.mul_le_mul_left 8 hmn)
    (Nat.mul_le_mul_left 49
      (Nat.pow_le_pow_right (by omega) hmn))

/-- The nonvanishing cutoff for the exact zeta Euler model is monotone in
the number of forms. -/
theorem complexZetaModelNonzeroCutoff_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexZetaModelNonzeroCutoff m ≤
      complexZetaModelNonzeroCutoff n := by
  unfold complexZetaModelNonzeroCutoff
  exact max_le_max
    (complexZetaModelComparisonCutoff_mono hmn)
    (Nat.mul_le_mul_left 4
      (complexZetaModelDifferenceNat_mono hmn))

















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





theorem complexArithmeticZetaRatioErrorNat_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexArithmeticZetaRatioErrorNat m ≤
      complexArithmeticZetaRatioErrorNat n := by
  unfold complexArithmeticZetaRatioErrorNat
  exact Nat.mul_le_mul_left 4
    (Nat.add_le_add
      (Nat.pow_le_pow_right (by omega) hmn)
      (complexZetaModelDifferenceNat_mono hmn))

theorem complexArithmeticZetaRatioErrorConstant_mono
    {m n : ℕ} (hmn : m ≤ n) :
    complexArithmeticZetaRatioErrorConstant m ≤
      complexArithmeticZetaRatioErrorConstant n := by
  rw [complexArithmeticZetaRatioErrorConstant_eq_natCast,
    complexArithmeticZetaRatioErrorConstant_eq_natCast]
  exact_mod_cast complexArithmeticZetaRatioErrorNat_mono hmn



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
/-- Every packaged canonical carry vector has arithmetic/zeta ratio
`1 + O_k(p⁻²)` above the common `k`-only cutoff. -/
theorem
    solution
    {k : ℕ} (hk : 2 ≤ k)
    (d : SelectedCFZCanonicalCarryFourierData k)
    (hR : 2 ≤ d.R) (p : Nat.Primes)
    (hpW : ¬(p : ℕ) ∣ primorial d.w)
    (hlarge :
      wTrickedCFZComplexExceptionalBound k < (p : ℕ)) :
    ‖d.primeArithmeticToZetaLocalRatio p - 1‖ ≤
      selectedCFZCarryEulerTailErrorConstant k /
        (p : ℝ) ^ 2 := by
  let : NeZero (p : ℕ) := ⟨p.prop.ne_zero⟩
  have horiginal :
      exceptionalPrimeBound
          (fun q : CFZFormIndex k => cfzAffineForm q) <
        (p : ℕ) :=
    (Nat.le_max_left _ _).trans_lt hlarge
  obtain ⟨hnonzero, hrankTwo⟩ :=
    selectedCFZCarryAdjustedFamilyAtVector_goodPrime
      (N := d.N) (W := primorial d.w) (b := d.b)
      hk p.prop hpW horiginal d.e d.carry
  have hfullCut :
      complexZetaModelNonzeroCutoff
          (Fintype.card (CFZFormIndex k)) ≤
        (p : ℕ) :=
    (Nat.le_max_right _ _).trans hlarge.le
  have hselectedCut :
      complexZetaModelNonzeroCutoff
          (Fintype.card (SelectedCFZFormIndex d.e)) ≤
        (p : ℕ) :=
    (complexZetaModelNonzeroCutoff_mono
      (card_selectedCFZFormIndex_le d.e)).trans hfullCut
  have hlocal :=
    norm_pairedFourierArithmeticToZetaLocalRatio_sub_one_le_of_goodPrime
      hnonzero hrankTwo hR hselectedCut d.t d.u
  have hconstant :
      complexArithmeticZetaRatioErrorConstant
          (Fintype.card (SelectedCFZFormIndex d.e)) ≤
        selectedCFZCarryEulerTailErrorConstant k :=
    complexArithmeticZetaRatioErrorConstant_mono
      (card_selectedCFZFormIndex_le d.e)
  unfold
    SelectedCFZCanonicalCarryFourierData.primeArithmeticToZetaLocalRatio
    SelectedCFZCanonicalCarryFourierData.carryAdjustedFamily
  exact hlocal.trans
    (div_le_div_of_nonneg_right hconstant
      (sq_nonneg (p : ℝ)))
