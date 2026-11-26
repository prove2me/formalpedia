-- Prove2me | Theorems.Thm_polytopeRoundedSupportDomain_boundaryParam
-- name    : polytopeRoundedSupportDomain_boundaryParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:42:58.98764+00:00
-- url     : https://prove2.me/theorems/71ef1693-c761-4af4-9645-0d9f1d9bbac2
-- title:
--   polytope Rounded Support Domain boundary Param: polytope Rounded Support Domain boundary Param
-- statement:
--   The polytope Rounded Support Domain boundary Param construction uses the polytope Rounded Support Domain boundary Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L111-L115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L111-L115

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace

theorem polytopeRoundedSupportDomain_boundaryParam
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (polytopeRoundedSupportDomain hu hdelta hrho).boundaryParam =
      polytopeRoundedSupportCurve u delta rho := by sorry

attribute [defeq] polytopeRoundedSupportDomain_boundaryParam
