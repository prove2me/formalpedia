-- Prove2me | Theorems.Thm_mul_adjoint_fourth_power_eq_symmetrized_sub_triple
-- name    : mul_adjoint_fourth_power_eq_symmetrized_sub_triple
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:48:00.969501+00:00
-- url     : https://prove2.me/theorems/feda8f3e-ff02-49b6-8928-53a9769f6050
-- title:
--   mul adjoint fourth power eq symmetrized sub triple: mul adjoint fourth power eq symmetrized sub triple
-- statement:
--   The exact C⋆-identity behind the short Ransford--Schwenninger version of
--   the Crouzeix--Palencia argument.  In the intended application `F = f(A)` and
--   `G = g(A)`, so multiplicativity identifies `F * G * F` with `(f g f)(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L112-L118
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/Palencia.lean#L112-L118

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Normal
import Definitions.Def_Operator_Crouzeix_Palencia
set_option autoImplicit false
open scoped InnerProductSpace

theorem mul_adjoint_fourth_power_eq_symmetrized_sub_triple
    {B : Type*} [NonUnitalNormedRing B] [StarRing B] [CStarRing B]
    (F G : B) :
    F * star F * F * star F =
      F * star (F + star G) * F * star F - F * G * F * star F := by sorry
