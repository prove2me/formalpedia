-- Prove2me | Theorems.Thm_exists_resolvent_affineOperator_neighborhood_bound
-- name    : exists_resolvent_affineOperator_neighborhood_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:50.854852+00:00
-- url     : https://prove2.me/theorems/8ecf8f23-4d86-4b20-826d-2a76ab01f1df
-- title:
--   exists resolvent affine Operator neighborhood bound: exists resolvent affine Operator neighborhood bound
-- statement:
--   The exists resolvent affine Operator neighborhood bound construction uses the exists resolvent affine Operator neighborhood bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L121-L206
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L121-L206

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem exists_resolvent_affineOperator_neighborhood_bound
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 ≤ C ∧
      ∀ w ∈ ball s epsilon, ∀ t : ℝ,
        Omega.boundaryParam t ∈ resolventSet ℂ (B + w • D) ∧
          ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤ C := by sorry
