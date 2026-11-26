-- Prove2me | Theorems.Thm_lipschitzWith_numericalRadius
-- name    : lipschitzWith_numericalRadius
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:22:23.613172+00:00
-- url     : https://prove2.me/theorems/ad69a24e-a5c2-4d4f-8b46-78b63782e7ea
-- title:
--   lipschitz With numerical Radius: lipschitz With numerical Radius
-- statement:
--   Numerical radius is `1`-Lipschitz with respect to the operator norm.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L293-L298
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/Radius.lean#L293-L298

import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Seminorm
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_NumericalRange_Radius
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem lipschitzWith_numericalRadius :
    LipschitzWith 1 (numericalRadius : (E →L[ℂ] E) → ℝ) := by sorry
