-- Prove2me | Theorems.Thm_norm_fourth_power_le_of_companion_calculus_bounds
-- name    : norm_fourth_power_le_of_companion_calculus_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:18.348797+00:00
-- url     : https://prove2.me/theorems/96939da9-ef42-4956-a284-c3dccb90d249
-- title:
--   norm fourth power le of companion calculus bounds: norm fourth power le of companion calculus bounds
-- statement:
--   If a functional calculus has an a priori norm bound `K`, the companion is
--   symmetrically bounded by `2m`, and multiplicativity plus companion contraction
--   bound `F G F` by `K m³`, then the published fourth-power estimate follows.
--   Taking `K` to be the best global calculus constant yields
--   `K⁴ ≤ 2K³ + K²`, whose positive fixed point is `1 + √2`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L165-L176
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L165-L176

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace

theorem norm_fourth_power_le_of_companion_calculus_bounds
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) {K m : ℝ} (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hsymm : ‖F + star G‖ ≤ 2 * m) (hF : ‖F‖ ≤ K * m)
    (htriple : ‖F * G * F‖ ≤ K * m ^ 3) :
    ‖F‖ ^ 4 ≤ (2 * K ^ 3 + K ^ 2) * m ^ 4 := by sorry
