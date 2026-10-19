-- Prove2me | Theorems.Thm_actuarial_d_dependence_changes_joint_annuity
-- name    : actuarial_d_dependence_changes_joint_annuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:06:26.764921+00:00
-- url     : https://prove2.me/theorems/b8682b43-79ae-4c0e-b376-2252b5a5304f
-- title:
--   Dependence changes joint annuity present value
-- statement:
--   Dependence changes joint annuity present value. Two lives with identical marginal survival curves have different joint-life annuity values. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   a_{xy}^{\text{paired}}\ne a_{xy}^{\text{product}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_annJoint
import Definitions.Def_actuarial_d_perfectPairLaw
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem actuarial_d_dependence_changes_joint_annuity  : annJoint 1 2 perfectPairLaw (fun _ => 1) (fun _ => 1) ≠ annJoint 1 2 productPairLaw (fun _ => 1) (fun _ => 1) := by sorry
