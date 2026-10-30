-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_QuasiPowers
-- name    : AnalyticCombinatorics_Ch9_LimitLaws_QuasiPowers
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T10:31:53.594853+00:00
-- url     : https://prove2.me/theorems/1958594b-6fe3-4f1c-bfcf-be9eb90b9388
-- title:
--   Normalized Fourier arguments
-- statement:
--   qpZ(beta,u2,n,t)=i*((sqrt(beta(n)*u2))^(-1)*t), embedding the real scaled argument into the complex numbers. Real square root and inverse are totalized at early nonpositive scales; eventual positivity follows only under the theorem premises.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/QuasiPowers.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Order.Filter.ENNReal

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Quasi-powers and Gaussian limit laws

This file formalizes the Mathlib-supported core of Hwang's quasi-powers theorem.

Mathlib v4.29.0 has Levy's continuity theorem for characteristic functions as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, but not a
corresponding Curtiss-style continuity theorem for moment-generating functions.
Accordingly the main limit theorem below takes a logarithmic quasi-powers expansion
on the imaginary axis, proves convergence of normalized characteristic functions,
and then applies Levy's theorem.
-/

noncomputable section

open Asymptotics Complex Filter MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The imaginary scaling point used by the normalized characteristic functions. -/
def qpZ (β : ℕ → ℝ) (u₂ : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.I * (((Real.sqrt (β n * u₂))⁻¹ * t : ℝ) : ℂ)

section MomentExtraction

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β ε₁ ε₂ : ℕ → ℝ} {u₁ u₂ : ℝ}

end MomentExtraction

section QuasiPowers

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)}
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β : ℕ → ℝ} {u₁ u₂ : ℝ} {R : ℕ → ℂ → ℂ} {V : ℂ → ℂ}

variable [∀ n, IsProbabilityMeasure (P n)]

end QuasiPowers

end LimitLaws
end Ch9
end AnalyticCombinatorics


