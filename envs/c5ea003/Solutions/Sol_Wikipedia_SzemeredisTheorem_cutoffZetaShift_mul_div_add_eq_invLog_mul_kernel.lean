-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cutoffZetaShift_mul_div_add_eq_invLog_mul_kernel
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:29.372661+00:00
-- url     : https://prove2.me/submissions/398e9a25-0666-42e2-ad1c-e8965f0e9af0

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerIntegral
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_CutoffNormalizerProduct
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_FourierZetaParameters
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierProductTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourierTail
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaEulerProductIdentification
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
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section



/-!
# The cutoff zeta pole as the normalizer kernel

For the Fourier shift

`z_R(t) = (1 - 2πit) / log R`,

the elementary pole contribution in one completed zeta quotient is

`z_R(t) z_R(u) / (z_R(t) + z_R(u))`.

This file identifies it exactly with `1 / log R` times the archimedean
kernel evaluated in `CutoffNormalizerIntegral`.  The identity is then
multiplied over a finite selected family and combined with both products of
cutoff Fourier transforms.  No limit is taken here: these are exact
algebraic normalization formulas.
-/

namespace Wikipedia.SzemeredisTheorem

open MeasureTheory
open scoped BigOperators

namespace SmoothSieveCutoff

/-- The two differentiated frequency weights add to the denominator of
the cutoff-normalizer kernel. -/
theorem cutoffDerivativeFrequencyWeight_add
    (t u : ℝ) :
    cutoffDerivativeFrequencyWeight t +
        cutoffDerivativeFrequencyWeight u =
      cutoffNormalizerDenominator t u := by
  simp only [cutoffDerivativeFrequencyWeight,
    cutoffNormalizerDenominator]
  push_cast
  ring

/-- The normalizer denominator is nonzero; its real part is `2`. -/
theorem cutoffNormalizerDenominator_ne_zero
    (t u : ℝ) :
    cutoffNormalizerDenominator t u ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [cutoffNormalizerDenominator] at hre

end SmoothSieveCutoff







end Wikipedia.SzemeredisTheorem

end
/-!
# The cutoff zeta pole as the normalizer kernel

For the Fourier shift

`z_R(t) = (1 - 2πit) / log R`,

the elementary pole contribution in one completed zeta quotient is

`z_R(t) z_R(u) / (z_R(t) + z_R(u))`.

This file identifies it exactly with `1 / log R` times the archimedean
kernel evaluated in `CutoffNormalizerIntegral`.  The identity is then
multiplied over a finite selected family and combined with both products of
cutoff Fourier transforms.  No limit is taken here: these are exact
algebraic normalization formulas.
-/
open Wikipedia.SzemeredisTheorem
open MeasureTheory
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- Exact one-pair conversion from the cutoff zeta pole to the
archimedean normalizer kernel. -/
theorem solution
    {R : ℕ} (hR : 1 < R) (t u : ℝ) :
    (cutoffZetaShift R t *
          cutoffZetaShift R u) /
        (cutoffZetaShift R t +
          cutoffZetaShift R u) =
      (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ) *
        SmoothSieveCutoff.cutoffNormalizerKernel t u := by
  let c : ℂ :=
    (((Real.log (R : ℝ))⁻¹ : ℝ) : ℂ)
  let a : ℂ :=
    SmoothSieveCutoff.cutoffDerivativeFrequencyWeight t
  let b : ℂ :=
    SmoothSieveCutoff.cutoffDerivativeFrequencyWeight u
  have hlog :
      Real.log (R : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hR)).ne'
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero hlog
  have hab : a + b ≠ 0 := by
    rw [SmoothSieveCutoff.cutoffDerivativeFrequencyWeight_add]
    exact
      SmoothSieveCutoff.cutoffNormalizerDenominator_ne_zero t u
  have ht :
      cutoffZetaShift R t = c * a := by
    rfl
  have hu :
      cutoffZetaShift R u = c * b := by
    rfl
  have hkernel :
      SmoothSieveCutoff.cutoffNormalizerKernel t u =
        a * b / (a + b) := by
    rw [SmoothSieveCutoff.cutoffNormalizerKernel,
      ← SmoothSieveCutoff.cutoffDerivativeFrequencyWeight_add]
  rw [ht, hu, hkernel]
  change
    (c * a * (c * b)) / (c * a + c * b) =
      c * (a * b / (a + b))
  field_simp [hc, hab]
