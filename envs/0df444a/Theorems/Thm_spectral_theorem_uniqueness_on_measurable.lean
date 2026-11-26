-- Prove2me | Theorems.Thm_spectral_theorem_uniqueness_on_measurable
-- name    : spectral_theorem_uniqueness_on_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:38.019802+00:00
-- url     : https://prove2.me/theorems/108f75e4-33bf-57e7-8062-32020e605ebc
-- title:
--   spectral theorem uniqueness on measurable: spectral theorem uniqueness on measurable
-- statement:
--   Two PVM representations of the same self-adjoint operator agree on every measurable set.
--
--   This is the extensional uniqueness statement supported by the current `PVM` definition, whose
--   axioms constrain `proj` only on measurable sets.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean#L318-L341
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean#L318-L341

import Definitions.Def_Spectral_Stone_Theorem
import Definitions.Def_Spectral_Spectral_FuncCalc
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Definitions.Def_Spectral_Spectral_Uniqueness
set_option autoImplicit false
open Filter MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem spectral_theorem_uniqueness_on_measurable
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S := by sorry
