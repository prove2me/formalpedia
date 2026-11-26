-- Prove2me | Theorems.Thm_polytopeRoundedSupportDomainOfRange_carrier
-- name    : polytopeRoundedSupportDomainOfRange_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:32.848843+00:00
-- url     : https://prove2.me/theorems/d585a940-761d-4e08-aa25-40f3382f6424
-- title:
--   polytope Rounded Support Domain Of Range carrier: polytope Rounded Support Domain Of Range carrier
-- statement:
--   The polytope Rounded Support Domain Of Range carrier construction uses the polytope Rounded Support Domain Of Range carrier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L49-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L49-L58

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace

theorem polytopeRoundedSupportDomainOfRange_carrier
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (hrange : Set.range (polytopeRoundedSupportCurve u delta rho) =
      frontier (smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho))) :
    (polytopeRoundedSupportDomainOfRange
      hu hdelta hrho hrange).carrier =
      smoothSupportOpenEnvelope
        (polytopeRoundedSupport u delta rho) := by sorry

attribute [defeq] polytopeRoundedSupportDomainOfRange_carrier
