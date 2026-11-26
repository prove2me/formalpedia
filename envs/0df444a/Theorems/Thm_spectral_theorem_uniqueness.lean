-- Prove2me | Theorems.Thm_spectral_theorem_uniqueness
-- name    : spectral_theorem_uniqueness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:10:36.463671+00:00
-- url     : https://prove2.me/theorems/1adf3ab5-dc80-5fb9-b704-2b6a4e53ab51
-- title:
--   spectral theorem uniqueness: spectral theorem uniqueness
-- statement:
--   Two PVM representations of the same self-adjoint operator agree on every measurable set.
--
--   Literal equality of the `PVM` structures is not implied because their laws intentionally leave
--   `proj S` unconstrained when `S` is nonmeasurable.
--
--   Source: https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean#L368-L375
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Spectral/Uniqueness.lean#L368-L375

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

theorem spectral_theorem_uniqueness
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (E₁ E₂ : PVM E)
    (h₁ : E₁.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (h₂ : E₂.unboundedIntegral ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable = A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S := by sorry
