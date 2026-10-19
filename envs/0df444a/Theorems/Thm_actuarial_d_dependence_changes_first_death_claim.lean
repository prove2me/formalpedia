-- Prove2me | Theorems.Thm_actuarial_d_dependence_changes_first_death_claim
-- name    : actuarial_d_dependence_changes_first_death_claim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:08:50.1385+00:00
-- url     : https://prove2.me/theorems/0cc36769-9127-497e-83bc-df0976359d05
-- title:
--   Dependence changes first-death insurance value
-- statement:
--   Dependence changes first-death insurance value. The first death occurs with different probabilities under coherent laws sharing both individual margins. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   A^{(1)}_{\text{paired}}\ne A^{(1)}_{\text{product}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 10, Section 10.6, p. 404. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://doi.org/10.1017/9781108784184

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_perfectPairLaw
import Definitions.Def_actuarial_d_productPairLaw

open ActuarialJointD

theorem actuarial_d_dependence_changes_first_death_claim  : assureFirst 1 perfectPairLaw (fun _ => 1) ≠ assureFirst 1 productPairLaw (fun _ => 1) := by sorry
