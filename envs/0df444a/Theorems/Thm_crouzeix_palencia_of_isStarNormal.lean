-- Prove2me | Theorems.Thm_crouzeix_palencia_of_isStarNormal
-- name    : crouzeix_palencia_of_isStarNormal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:33.344697+00:00
-- url     : https://prove2.me/theorems/b735ee6f-66ea-57d1-88a0-8cc8a9371db8
-- title:
--   crouzeix palencia of is Star Normal: crouzeix palencia of is Star Normal
-- statement:
--   The Crouzeix--Palencia conclusion for a normal operator.  In this branch
--   the sharper constant `1` follows from the continuous functional calculus and
--   the polynomial spectral mapping theorem; monotonicity then gives the stated
--   `1 + √2` constant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L855-L869
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L855-L869

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem crouzeix_palencia_of_isStarNormal (A : E →L[ℂ] E) [IsStarNormal A] :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2) (closure (numericalRange A)) := by sorry
