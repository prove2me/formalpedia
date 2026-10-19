-- Prove2me | Theorems.Thm_actuarial_d_same_margins_different_joint
-- name    : actuarial_d_same_margins_different_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:06:14.278441+00:00
-- url     : https://prove2.me/theorems/99be33ec-0e54-42e4-9bfe-65d64c6ec98e
-- title:
--   Same single-life margins, different joint survival
-- statement:
--   Same single-life margins, different joint survival. The coherent diagonal and product joint laws have equal survival margins but genuinely different dependence. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_x=p_y=\tfrac12,\quad p_{xy}^{\text{paired}}\ne p_{xy}^{\text{product}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_px
import Definitions.Def_actuarial_d_py
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_perfectPairLaw
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem actuarial_d_same_margins_different_joint  : px 1 perfectPairLaw 1 = px 1 productPairLaw 1 ∧ py 1 perfectPairLaw 1 = py 1 productPairLaw 1 ∧ pxy 1 perfectPairLaw 1 ≠ pxy 1 productPairLaw 1 := by sorry
