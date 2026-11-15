-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.integrable_cutoffNormalizerSeparatedProduct
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:42:40.27841+00:00
-- url     : https://prove2.me/submissions/3162bec5-d2e9-4b74-a75c-7256e71e97af

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_SmoothSieveCutoff_cutoffNormalizerFourierIntegrand_integrable

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# The archimedean cutoff normalizer integral

For Mathlib's analyst Fourier normalization, put

`F(t) = 𝓕 (x ↦ exp(x) χ(x))(t)`

and

`W(t) = 1 - 2 π i t`.

The one-pair archimedean factor in the Goldston--Yıldırım calculation is

`∫ t, ∫ u, F(t) F(u) W(t) W(u) /
  (2 - 2 π i (t + u))`.

This file identifies it with the derivative-square normalizer

`∫_{0 < x} |χ'(x)|² dx`.

The proof records both analytic ingredients explicitly.  First,
`W(t) F(t)` is the Fourier transform of
`x ↦ -exp(x) χ'(x)`.  Second, the reciprocal denominator is the Laplace
integral

`∫_{0 < x} exp((-2 + 2 π i (t + u))x) dx`.

The remaining argument is an absolutely convergent Fubini interchange.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Function MeasureTheory Set
open scoped BigOperators FourierTransform LineDeriv SchwartzMap

namespace SmoothSieveCutoff

/-! ## The differentiated Fourier input -/

















/-! It is useful below to give the differentiated transform a short
name. -/











/-! ## The Laplace kernel -/



















/-! ## Absolute convergence of the three-variable integral -/









/-! ## Fubini and factorization -/







/-- The abbreviated integrand is exactly the original expression with
two cutoff transforms and the one-pair kernel. -/
theorem cutoffFourierTransform_mul_cutoffNormalizerKernel
    (χ : SmoothSieveCutoff) (t u : ℝ) :
    χ.cutoffFourierTransform t *
        χ.cutoffFourierTransform u *
        cutoffNormalizerKernel t u =
      χ.cutoffNormalizerFourierIntegrand t u := by
  simp only [cutoffNormalizerKernel,
    cutoffNormalizerFourierIntegrand,
    cutoffWeightedFourier,
    div_eq_mul_inv]
  ring







/-! ## The one-pair archimedean identity -/



/-- Absolute integrability of the original, unabbreviated one-pair
Fourier integrand. -/
theorem cutoffFourierKernelIntegrand_integrable
    (χ : SmoothSieveCutoff) :
    Integrable
      (fun z : ℝ × ℝ =>
        χ.cutoffFourierTransform z.1 *
          χ.cutoffFourierTransform z.2 *
          cutoffNormalizerKernel z.1 z.2)
      (volume.prod volume) := by
  exact χ.cutoffNormalizerFourierIntegrand_integrable.congr
    (Filter.Eventually.of_forall fun z => by
      exact
        (χ.cutoffFourierTransform_mul_cutoffNormalizerKernel
          z.1 z.2).symm)



end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem

end

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









/-- Absolute integrability of the paired finite product. -/
theorem integrable_cutoffNormalizerPairedProduct
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (χ.cutoffNormalizerPairedProduct :
        (κ → ℝ × ℝ) → ℂ) := by
  rw [MeasureTheory.volume_pi]
  exact Integrable.fintype_prod fun _ =>
    χ.cutoffFourierKernelIntegrand_integrable



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
/-- Absolute integrability in the separated coordinate convention. -/
theorem solution
    {κ : Type*} [Fintype κ]
    (χ : SmoothSieveCutoff) :
    Integrable
      (χ.cutoffNormalizerSeparatedProduct :
        ((κ → ℝ) × (κ → ℝ)) → ℂ)
      (volume.prod volume) := by
  let e :=
    MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ κ
  have hpreserving :
      MeasurePreserving e
        (volume : Measure (κ → ℝ × ℝ))
        ((volume : Measure (κ → ℝ)).prod
          (volume : Measure (κ → ℝ))) :=
    volume_measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ κ
  have hcomp :
      Integrable
        ((χ.cutoffNormalizerSeparatedProduct :
            ((κ → ℝ) × (κ → ℝ)) → ℂ) ∘ e) := by
    change
      Integrable
        (fun z : κ → ℝ × ℝ =>
          χ.cutoffNormalizerSeparatedProduct
            (MeasurableEquiv.arrowProdEquivProdArrow
              ℝ ℝ κ z))
    exact
      χ.integrable_cutoffNormalizerPairedProduct.congr
        (Filter.Eventually.of_forall fun z =>
          (χ.cutoffNormalizerSeparatedProduct_arrowProdEquiv
            z).symm)
  exact
    (hpreserving.integrable_comp_emb
      e.measurableEmbedding).mp hcomp
