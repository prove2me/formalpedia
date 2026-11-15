-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integral_cutoffNormalizerSeparatedProduct_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:45:10.997704+00:00
-- url     : https://prove2.me/submissions/664d3f56-505b-45f7-ab4a-c2eadc3b609f

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_integral_cutoffNormalizerPairFactor_eq_normalizer

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# Finite products of the cutoff-normalizer integral

The one-pair archimedean calculation in
`CutoffNormalizerIntegral` is the factor which remains for each selected
linear form after the arithmetic Euler product has been replaced by its
zeta model.  This file tensors that calculation over an arbitrary finite
family.

Both useful coordinate arrangements are recorded:

* a function `κ → ℝ × ℝ`, which makes the integrand a literal product of
  one-pair factors; and
* the sieve convention `(κ → ℝ) × (κ → ℝ)`, with the two copies of the
  Fourier variables separated.

The passage between them uses Mathlib's measure-preserving equivalence
between functions into a product and pairs of functions.  Thus the final
identity has exactly the product measure used by the multivariate divisor
expansion.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

namespace SmoothSieveCutoff











/-- Tensorized one-pair identity in paired coordinates. -/
theorem integral_cutoffNormalizerPairedProduct_eq_pow
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    (∫ z : κ → ℝ × ℝ,
        χ.cutoffNormalizerPairedProduct z) =
      (χ.normalizer : ℂ) ^ Fintype.card κ := by
  unfold cutoffNormalizerPairedProduct
  rw [integral_fintype_prod_volume_eq_pow,
    χ.integral_cutoffNormalizerPairFactor_eq_normalizer]

/-- The paired and separated product integrands agree under the canonical
function/product equivalence. -/
theorem cutoffNormalizerSeparatedProduct_arrowProdEquiv
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) (z : κ → ℝ × ℝ) :
    χ.cutoffNormalizerSeparatedProduct
        (MeasurableEquiv.arrowProdEquivProdArrow
          ℝ ℝ κ z) =
      χ.cutoffNormalizerPairedProduct z := by
  rfl





end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end
/-!
# Finite products of the cutoff-normalizer integral

The one-pair archimedean calculation in
`CutoffNormalizerIntegral` is the factor which remains for each selected
linear form after the arithmetic Euler product has been replaced by its
zeta model.  This file tensors that calculation over an arbitrary finite
family.

Both useful coordinate arrangements are recorded:

* a function `κ → ℝ × ℝ`, which makes the integrand a literal product of
  one-pair factors; and
* the sieve convention `(κ → ℝ) × (κ → ℝ)`, with the two copies of the
  Fourier variables separated.

The passage between them uses Mathlib's measure-preserving equivalence
between functions into a product and pairs of functions.  Thus the final
identity has exactly the product measure used by the multivariate divisor
expansion.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff

open Wikipedia.SzemeredisTheorem.SmoothSieveCutoff in
/-- **Finite-product archimedean identity.**  In the separated Fourier
coordinate convention, the full integral is the `card κ`-th power of the
cutoff normalizer. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    (∫ tu :
        (κ → ℝ) × (κ → ℝ),
        χ.cutoffNormalizerSeparatedProduct tu
          ∂(volume.prod volume)) =
      (χ.normalizer : ℂ) ^ Fintype.card κ := by
  let e :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ
  have hpreserving :
      MeasurePreserving e
        (volume : Measure (κ → ℝ × ℝ))
        ((volume : Measure (κ → ℝ)).prod
          (volume : Measure (κ → ℝ))) :=
    volume_measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ κ
  calc
    (∫ tu :
        (κ → ℝ) × (κ → ℝ),
        χ.cutoffNormalizerSeparatedProduct tu
          ∂(volume.prod volume)) =
        ∫ z : κ → ℝ × ℝ,
          χ.cutoffNormalizerSeparatedProduct (e z) := by
      exact
        (hpreserving.integral_comp'
          χ.cutoffNormalizerSeparatedProduct).symm
    _ =
        ∫ z : κ → ℝ × ℝ,
          χ.cutoffNormalizerPairedProduct z := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z =>
        χ.cutoffNormalizerSeparatedProduct_arrowProdEquiv z
    _ =
        (χ.normalizer : ℂ) ^ Fintype.card κ :=
      χ.integral_cutoffNormalizerPairedProduct_eq_pow
