-- Prove2me | Theorems.Thm_norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
-- name    : norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:45:58.648051+00:00
-- url     : https://prove2.me/theorems/93fbd0aa-b8f5-556a-9ff8-b8d120683307
-- title:
--   norm le one add sqrt two mul of auxiliary re inner lower bounds: norm le one add sqrt two mul of auxiliary re inner lower bounds
-- statement:
--   The Crouzeix--Palencia balance only uses the lower real part of the
--   auxiliary product.  In the identity
--   `F F† = F (F + G†)† - F G`, an upper bound for `F F†` requires only
--   `-m² ≤ re ⟪x, F G x⟫` on unit vectors.  No bound on the modulus, numerical
--   radius, or operator norm of `F G` is needed.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L695-L764
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L695-L764

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem norm_le_one_add_sqrt_two_mul_of_auxiliary_re_inner_lower_bounds
    (F G : E →L[ℂ] E) {m : ℝ}
    (hsymm : ‖F + star G‖ ≤ 2 * m)
    (hprod : ∀ x : E, ‖x‖ = 1 →
      -(m ^ 2) ≤ RCLike.re ⟪x, (F * G) x⟫_ℂ) :
    ‖F‖ ≤ (1 + Real.sqrt 2) * m := by sorry
