-- Prove2me | Theorems.Thm_numericalRange_smul_add_smul_one
-- name    : numericalRange_smul_add_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:07.515893+00:00
-- url     : https://prove2.me/theorems/aefe8a61-67fa-5ee3-8676-4cd0b4db79c7
-- title:
--   numerical Range smul add smul one: numerical Range smul add smul one
-- statement:
--   The numerical range commutes with the usual affine action
--   `A ↦ aA + bI`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/AffineClosure.lean#L19-L23
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/AffineClosure.lean#L19-L23

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_AffineClosure
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem numericalRange_smul_add_smul_one
    (A : E →L[ℂ] E) (a b : ℂ) :
    numericalRange (a • A + b • 1) =
      (fun z => a * z + b) '' numericalRange A := by sorry
