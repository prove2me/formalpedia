-- Prove2me | Theorems.Thm_polytopeRoundedSupportDomain_carrier
-- name    : polytopeRoundedSupportDomain_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:42:36.869511+00:00
-- url     : https://prove2.me/theorems/bd49a719-7e0c-5114-9423-a63200df71f6
-- title:
--   polytope Rounded Support Domain carrier: polytope Rounded Support Domain carrier
-- statement:
--   The polytope Rounded Support Domain carrier construction uses the polytope Rounded Support Domain carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L104-L109
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L104-L109

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace

theorem polytopeRoundedSupportDomain_carrier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    (polytopeRoundedSupportDomain hu hdelta hrho).carrier =
      smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho) := by sorry

attribute [defeq] polytopeRoundedSupportDomain_carrier
