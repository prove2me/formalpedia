-- Prove2me | Theorems.Thm_le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
-- name    : le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:43.499504+00:00
-- url     : https://prove2.me/theorems/596372a4-2717-5daf-a395-2d1b7093d11c
-- title:
--   le one add sqrt two of fourth le two mul cube add sq: le one add sqrt two of fourth le two mul cube add sq
-- statement:
--   The nonnegative fixed point of the Ransford--Schwenninger fourth-power
--   bootstrap is at most `1 + √2`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L225-L239
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L225-L239

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace

theorem le_one_add_sqrt_two_of_fourth_le_two_mul_cube_add_sq
    {K : ℝ} (hK : 0 ≤ K) (hfour : K ^ 4 ≤ 2 * K ^ 3 + K ^ 2) :
    K ≤ 1 + Real.sqrt 2 := by sorry
