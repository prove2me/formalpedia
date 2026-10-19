-- Prove2me | Theorems.Thm_actuarial_d_perfect_pair_joint
-- name    : actuarial_d_perfect_pair_joint
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:04:16.163137+00:00
-- url     : https://prove2.me/theorems/cb8020dc-7c8a-49dc-bc84-a622faf010f7
-- title:
--   Both-alive probability under perfect dependence
-- statement:
--   Both-alive probability under perfect dependence. The equal-death-state probability gives joint survival of one half at the next anniversary. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   p_{xy}^{\text{paired}}(1)=\tfrac12
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_pxy
import Definitions.Def_actuarial_d_perfectPairLaw

open ActuarialJointD

theorem actuarial_d_perfect_pair_joint  : pxy 1 perfectPairLaw 1 = (1/2 : ℝ) := by sorry
