-- Prove2me | Theorems.Thm_actuarial_d_product_pair_joint
-- name    : actuarial_d_product_pair_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:04:27.875884+00:00
-- url     : https://prove2.me/theorems/78fc2c9b-67c1-41cf-bb31-00f8b7bde6ff
-- title:
--   Both-alive probability under independence
-- statement:
--   Both-alive probability under independence. Independent equally likely survival gives joint survival one quarter at the next anniversary. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{xy}^{\text{product}}(1)=\tfrac14
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem actuarial_d_product_pair_joint  : pxy 1 productPairLaw 1 = (1/4 : ℝ) := by sorry
