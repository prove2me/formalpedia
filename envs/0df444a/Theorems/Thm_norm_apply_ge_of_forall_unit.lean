-- Prove2me | Theorems.Thm_norm_apply_ge_of_forall_unit
-- name    : norm_apply_ge_of_forall_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:52.547948+00:00
-- url     : https://prove2.me/theorems/449c5616-ffd3-4a4d-91f2-7bc2763fd926
-- title:
--   norm apply ge of forall unit: norm apply ge of forall unit
-- statement:
--   A lower bound `d ≤ ‖⟪x, B x⟫_ℂ‖` on unit vectors gives `d * ‖x‖ ≤ ‖B x‖` for all `x`
--   (homogeneity of the quadratic form, then Cauchy–Schwarz).
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean#L38-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean#L38-L54

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_apply_ge_of_forall_unit (B : E →L[ℂ] E) {d : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, B x⟫_ℂ‖) (x : E) : d * ‖x‖ ≤ ‖B x‖ := by sorry
