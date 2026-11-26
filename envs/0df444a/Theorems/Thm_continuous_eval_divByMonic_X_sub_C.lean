-- Prove2me | Theorems.Thm_continuous_eval_divByMonic_X_sub_C
-- name    : continuous_eval_divByMonic_X_sub_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:22.518703+00:00
-- url     : https://prove2.me/theorems/405c7682-c15d-4bfe-ad9b-661d451a2fe1
-- title:
--   continuous eval div By Monic X sub C: continuous eval div By Monic X sub C
-- statement:
--   The value of the polynomial divided difference
--   `p /ₘ (X - C xi)` at `sigma` depends jointly continuously on `xi` and
--   `sigma`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L112-L130
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L112-L130

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem continuous_eval_divByMonic_X_sub_C (p : Polynomial ℂ) :
    Continuous (fun x : ℂ × ℂ =>
      Polynomial.eval x.2 (p /ₘ (Polynomial.X - Polynomial.C x.1))) := by sorry
