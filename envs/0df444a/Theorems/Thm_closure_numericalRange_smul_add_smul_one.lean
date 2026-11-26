-- Prove2me | Theorems.Thm_closure_numericalRange_smul_add_smul_one
-- name    : closure_numericalRange_smul_add_smul_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:13.829404+00:00
-- url     : https://prove2.me/theorems/c53510f8-6bca-5458-b2d3-893026d4f566
-- title:
--   closure numerical Range smul add smul one: closure numerical Range smul add smul one
-- statement:
--   A nondegenerate affine change of an operator transports the closure of
--   its numerical range by the same affine map.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/AffineClosure.lean#L27-L39
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/NumericalRange/AffineClosure.lean#L27-L39

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_AffineClosure
set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem closure_numericalRange_smul_add_smul_one
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    closure (numericalRange (a • A + b • 1)) =
      (fun z => a * z + b) '' closure (numericalRange A) := by sorry
