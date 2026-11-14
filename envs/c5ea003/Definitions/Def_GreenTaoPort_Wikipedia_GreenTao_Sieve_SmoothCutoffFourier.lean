-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoffFourier
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:49:31.45603+00:00
-- url     : https://prove2.me/theorems/5e8ff2fa-b7f3-4e49-8714-b825cab8277a
-- title:
--   Fourier inversion data for an exponentially tilted sieve cutoff
-- statement:
--   For a smooth sieve cutoff $\chi$, the complex-valued Fourier input is $g(x)=e^x\chi(x)$. The bundle supplies this compactly supported smooth function as a Schwartz function, its analyst-normalized Fourier transform $F_\chi=\mathcal Fg$, and the same transform with its Schwartz structure retained.
--
--   The inverse character is $e^{2\pi i tx}$. Removing the exponential tilt gives the multiplicative phase
--
--   $$
--   e^{-x+2\pi i tx},
--   $$
--
--   and its divisor specialization substitutes $x=\log d/\log R$ for natural parameters $R,d$. All transform and phase conventions are explicit so that later divisor expansions use a consistent sign and factor $2\pi$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/SmoothCutoffFourier.lean#L37-L272

import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_SmoothCutoff
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Tactic
import Lean
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- The compactly supported function to which Fourier inversion is applied:
`g(x) = exp(x) χ(x)`, regarded as complex-valued. -/
noncomputable def fourierInput (χ : SmoothSieveCutoff) (x : ℝ) : ℂ :=
  ((Real.exp x * χ x : ℝ) : ℂ)

/-- The Fourier input is infinitely differentiable. -/
theorem fourierInput_contDiff (χ : SmoothSieveCutoff) :
    ContDiff ℝ ∞ χ.fourierInput := by
  have hspace :
      (NormedField.toNormedSpace : NormedSpace ℝ ℝ) =
        RCLike.toInnerProductSpaceReal.toNormedSpace :=
    NormedSpace.ext rfl
  rw [← hspace]
  change
    ContDiff ℝ ∞
      (Complex.ofRealCLM ∘ fun x : ℝ ↦ Real.exp x * χ.toFun x)
  exact
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.mul χ.smooth)

/-- The exponential factor does not enlarge the support of the cutoff. -/
theorem fourierInput_hasCompactSupport (χ : SmoothSieveCutoff) :
    HasCompactSupport χ.fourierInput := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-1) 1) isCompact_Icc
  intro x hx
  apply χ.support_subset
  intro hχ
  apply hx
  simp [fourierInput, hχ]

/-- The Fourier input packaged as a Schwartz function. -/
noncomputable def fourierInputSchwartz
    (χ : SmoothSieveCutoff) : 𝓢(ℝ, ℂ) :=
  χ.fourierInput_hasCompactSupport.toSchwartzMap χ.fourierInput_contDiff



/-- The Fourier transform of `x ↦ exp(x) χ(x)`, with Mathlib's analyst
normalization. -/
noncomputable def cutoffFourierTransform
    (χ : SmoothSieveCutoff) (t : ℝ) : ℂ :=
  𝓕 χ.fourierInput t

/-- The same transform, retaining its Schwartz-space structure. -/
noncomputable def cutoffFourierSchwartz
    (χ : SmoothSieveCutoff) : 𝓢(ℝ, ℂ) :=
  𝓕 χ.fourierInputSchwartz















/-- The positive-sign character in the inverse Fourier transform. -/
noncomputable def inverseFourierCharacter (x t : ℝ) : ℂ :=
  Complex.exp
    (((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I)









/-- The phase appearing after removing the factor `exp(x)` from the Fourier
input. -/
noncomputable def cutoffMultiplicativePhase (x t : ℝ) : ℂ :=
  Complex.exp
    (-(x : ℂ) +
      ((2 * Real.pi * (t * x) : ℝ) : ℂ) * Complex.I)









/-- The phase specialized to the logarithmic divisor variable. -/
noncomputable def divisorMultiplicativePhase
    (R d : ℕ) (t : ℝ) : ℂ :=
  cutoffMultiplicativePhase
    (Real.log d / Real.log R) t











end SmoothSieveCutoff

end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffFourierTransform.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.cutoffMultiplicativePhase.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.divisorMultiplicativePhase.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.fourierInput.eq_1,
    `Wikipedia.SzemeredisTheorem.SmoothSieveCutoff.inverseFourierCharacter.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


