-- Prove2me | Theorems.Thm_eq_smul_resolvent_apply_sub_apply
-- name    : eq_smul_resolvent_apply_sub_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:36.391845+00:00
-- url     : https://prove2.me/theorems/ae260777-cc93-434e-8edb-e45b4cd86116
-- title:
--   eq smul resolvent apply sub apply: eq smul resolvent apply sub apply
-- statement:
--   `x = σ • y - A y` for `y = R_A(σ) x` and `σ` in the resolvent set.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L46-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayer.lean#L46-L58

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem eq_smul_resolvent_apply_sub_apply (A : E →L[ℂ] E) {σ : ℂ}
    (hσ : σ ∈ resolventSet ℂ A) (x : E) :
    x = σ • resolvent A σ x - A (resolvent A σ x) := by sorry
