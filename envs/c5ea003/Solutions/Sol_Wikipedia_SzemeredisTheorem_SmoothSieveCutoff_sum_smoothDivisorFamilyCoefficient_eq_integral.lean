-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.sum_smoothDivisorFamilyCoefficient_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:42:36.343572+00:00
-- url     : https://prove2.me/submissions/685fd235-b712-4e55-967b-ed690e8d9ae6

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Geometry
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_ReducedResidues
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Primes_WTrick
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CongruenceAverage
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ExceptionalPrimes
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LinearFormsExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_LocalFactors
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_MultivariateFourierExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothMajorant
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
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
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_transformedDivisorFamilySide_eq_prod

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section





/-!
# Fourier inversion for the smooth sieve cutoff

This file supplies the analytic transform used in the Goldston--Yıldırım
calculation.  For a smooth sieve cutoff `χ`, put

`g(x) = exp(x) χ(x)`.

We regard `g` as complex-valued and use Mathlib's analyst normalization

`𝓕 g(t) = ∫ x, exp(-2 π i x t) g(x)`.

The function `g` is smooth and compactly supported, hence is a Schwartz
function.  Its Fourier transform is therefore again Schwartz and in
particular integrable.  Fourier inversion gives

`χ(x) = ∫ t, 𝓕 g(t) exp(-x + 2 π i t x)`.

At `x = log d / log R`, the last exponential is multiplicative in `d`.
The final results interchange this integral with the finite divisor sums
that occur in the truncated divisor sum.
-/

namespace Wikipedia.SzemeredisTheorem

open Function MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators FourierTransform
  ContDiff SchwartzMap

namespace SmoothSieveCutoff





















/-- The cutoff transform is integrable, as needed for pointwise Fourier
inversion. -/
theorem cutoffFourierTransform_integrable (χ : SmoothSieveCutoff) :
    Integrable χ.cutoffFourierTransform := by
  change Integrable (χ.cutoffFourierSchwartz : ℝ → ℂ)
  exact χ.cutoffFourierSchwartz.integrable









@[simp]
theorem norm_inverseFourierCharacter (x t : ℝ) :
    ‖inverseFourierCharacter x t‖ = 1 := by
  rw [inverseFourierCharacter, Complex.norm_exp]
  simp

theorem continuous_inverseFourierCharacter (x : ℝ) :
    Continuous (inverseFourierCharacter x) := by
  unfold inverseFourierCharacter
  fun_prop

/-- Multiplying the integrable Fourier transform by an inverse Fourier
character preserves integrability. -/
theorem integrable_cutoffFourierTransform_mul_inverseFourierCharacter
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t * inverseFourierCharacter x t) := by
  refine χ.cutoffFourierTransform_integrable.mul_bdd
    (c := 1) ?_ ?_
  · exact (continuous_inverseFourierCharacter x).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t ↦ by
      rw [norm_inverseFourierCharacter]





/-- The cutoff phase is the inverse Fourier character times the real
exponential `exp(-x)`. -/
theorem cutoffMultiplicativePhase_eq
    (x t : ℝ) :
    cutoffMultiplicativePhase x t =
      (Real.exp (-x) : ℂ) * inverseFourierCharacter x t := by
  simp only [cutoffMultiplicativePhase, inverseFourierCharacter,
    Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_exp]



/-- The integrand in the cutoff inversion formula is integrable. -/
theorem integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
    (χ : SmoothSieveCutoff) (x : ℝ) :
    Integrable
      (fun t : ℝ ↦
        χ.cutoffFourierTransform t *
          cutoffMultiplicativePhase x t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_inverseFourierCharacter x).mul_const
      (Real.exp (-x) : ℂ)
  convert h using 1
  funext t
  rw [cutoffMultiplicativePhase_eq]
  ring









/-- The integral occurring in a transformed divisor summand is integrable. -/
theorem integrable_transformedSmoothDivisorSummand
    (χ : SmoothSieveCutoff) (R d : ℕ) :
    Integrable
      (fun t : ℝ ↦
        (ArithmeticFunction.moebius d : ℂ) *
          χ.cutoffFourierTransform t *
            divisorMultiplicativePhase R d t) := by
  have h :=
    (χ.integrable_cutoffFourierTransform_mul_cutoffMultiplicativePhase
      (Real.log d / Real.log R)).const_mul
      (ArithmeticFunction.moebius d : ℂ)
  simpa only [divisorMultiplicativePhase, mul_assoc] using h





end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

section




/-!
# Multivariate Fourier rewrite of the divisor expansion

The finite Selberg-square expansion has two smooth divisor coefficients for
each form.  Fourier inversion turns those `2 * card κ` coefficients into a
single integral over two copies of `κ → ℝ`.

This file proves that rewrite exactly.  All sum/integral interchanges are
finite, while absolute integrability follows coordinatewise from the
Schwartz transform.  The arithmetic divisibility density is left as an
arbitrary real coefficient, ready for the Euler-product comparison.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators

namespace SmoothSieveCutoff



/-- The coordinatewise transformed divisor family is absolutely
integrable. -/
theorem integrable_transformedDivisorFamilySide
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (d : κ → ℕ) :
    Integrable (χ.transformedDivisorFamilySide R d :
      (κ → ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun q =>
    χ.integrable_transformedSmoothDivisorSummand R (d q)





/-- Absolute integrability of one full paired-family integrand. -/
theorem integrable_transformedPairedDivisorFamily
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    Integrable
      (χ.transformedPairedDivisorFamily R z)
      (volume.prod volume) :=
  (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).1)).mul_prod
    (χ.integrable_transformedDivisorFamilySide R
      (fun q => (z q).2))

/-- Product-space integral of a paired divisor family. -/
theorem integral_transformedPairedDivisorFamily_eq
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    (∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.transformedPairedDivisorFamily R z tu
        ∂(volume.prod volume)) =
      (∏ q,
          (smoothDivisorSummand
            χ.toFun R (z q).1 : ℂ)) *
        ∏ q,
          (smoothDivisorSummand
            χ.toFun R (z q).2 : ℂ) := by
  unfold transformedPairedDivisorFamily
  rw [integral_prod_mul,
    χ.integral_transformedDivisorFamilySide_eq_prod
      R (fun q => (z q).1),
    χ.integral_transformedDivisorFamilySide_eq_prod
      R (fun q => (z q).2)]

/-- Exact Fourier integral for the smooth coefficient of one paired divisor
family. -/
theorem smoothDivisorFamilyCoefficient_eq_integral
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (z : κ → ℕ × ℕ) :
    (smoothDivisorFamilyCoefficient χ.toFun R z : ℂ) =
      ∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.transformedPairedDivisorFamily R z tu
        ∂(volume.prod volume) := by
  rw [χ.integral_transformedPairedDivisorFamily_eq R z]
  unfold smoothDivisorFamilyCoefficient
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl









end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# Multivariate Fourier rewrite of the divisor expansion

The finite Selberg-square expansion has two smooth divisor coefficients for
each form.  Fourier inversion turns those `2 * card κ` coefficients into a
single integral over two copies of `κ → ℝ`.

This file proves that rewrite exactly.  All sum/integral interchanges are
finite, while absolute integrability follows coordinatewise from the
Schwartz transform.  The arithmetic divisibility density is left as an
arbitrary real coefficient, ready for the Euler-product comparison.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- **Exact multivariate Fourier rewrite.**  The whole finite sum of smooth
paired-divisor coefficients is one absolutely convergent product-space
integral. -/
theorem solution
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (χ : SmoothSieveCutoff) (R : ℕ)
    (density : (κ → ℕ × ℕ) → ℝ) :
    ((∑ z ∈ smoothDivisorFamilyChoices κ R,
        smoothDivisorFamilyCoefficient χ.toFun R z *
          density z : ℝ) : ℂ) =
      ∫ tu : (κ → ℝ) × (κ → ℝ),
        χ.divisorExpansionFourierIntegrand R density tu
        ∂(volume.prod volume) := by
  unfold divisorExpansionFourierIntegrand
  rw [MeasureTheory.integral_finsetSum]
  · push_cast
    apply Finset.sum_congr rfl
    intro z _hz
    rw [integral_const_mul,
      ← χ.smoothDivisorFamilyCoefficient_eq_integral R z]
    ring
  · intro z _hz
    exact
      (χ.integrable_transformedPairedDivisorFamily R z).const_mul
        (density z : ℂ)
