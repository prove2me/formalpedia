-- Prove2me | Theorems.Thm_numericalRange_eq_image
-- name    : numericalRange_eq_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:23:57.878839+00:00
-- url     : https://prove2.me/theorems/db181fe2-da55-4cc3-98f9-829fb8fc2c94
-- title:
--   numerical Range eq image: numerical Range eq image
-- statement:
--   The numerical range is the image of the unit sphere under `x ↦ ⟪x, A x⟫_ℂ`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean#L25-L28
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Compact.lean#L25-L28

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Compact
set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_eq_image (A : E →L[ℂ] E) :
    numericalRange A = (fun x => ⟪x, A x⟫_ℂ) '' Metric.sphere (0 : E) 1 := by sorry
