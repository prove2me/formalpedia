-- Prove2me | Theorems.Thm_image_Ico_eq_range_of_periodic
-- name    : image_Ico_eq_range_of_periodic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:13.048572+00:00
-- url     : https://prove2.me/theorems/d1939937-7a8d-4649-80c9-7455f7cf9424
-- title:
--   image Ico eq range of periodic: image Ico eq range of periodic
-- statement:
--   A positive-periodic function has the same range on any half-open
--   fundamental interval as it does on the whole real line.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L210-L217
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportCurveRange.lean#L210-L217

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff

theorem image_Ico_eq_range_of_periodic
    {α : Type*} {f : ℝ → α} {p : ℝ}
    (hp : Function.Periodic f p) (hp_pos : 0 < p) (a : ℝ) :
    f '' Ico a (a + p) = range f := by sorry
