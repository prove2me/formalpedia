-- Prove2me | Theorems.Thm_isUnit_of_forall_norm_le
-- name    : isUnit_of_forall_norm_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:35:04.918037+00:00
-- url     : https://prove2.me/theorems/95a348ac-e0b1-5041-9de6-064a900107bd
-- title:
--   is Unit of forall norm le: is Unit of forall norm le
-- statement:
--   An operator bounded below (`d * ‖x‖ ≤ ‖B x‖`, `d > 0`) whose adjoint is bounded below is a
--   unit: it is injective with closed range, and the range is dense because its orthogonal complement
--   is the kernel of the adjoint.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean#L61-L84
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/SpectralSet/SpectrumInNR.lean#L61-L84

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
variable [CompleteSpace E]

theorem isUnit_of_forall_norm_le (B : E →L[ℂ] E) {d : ℝ} (hd : 0 < d)
    (hB : ∀ x, d * ‖x‖ ≤ ‖B x‖) (hB' : ∀ x, d * ‖x‖ ≤ ‖(adjoint B) x‖) : IsUnit B := by sorry
