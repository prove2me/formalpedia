-- Prove2me | Theorems.Thm_actuarial_d_advanced_occupation_reconciliation
-- name    : actuarial_d_advanced_occupation_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T11:29:47.27545+00:00
-- url     : https://prove2.me/theorems/b375b718-e105-41e0-8f8a-d4f528e431d7
-- title:
--   Complex survivor contract as separate entitlement values
-- statement:
--   Complex survivor contract as separate entitlement values. One expectation of realised paths agrees with a guaranteed member annuity, a delayed spouse annuity and actual death riders. The settlement date, survivor entitlement, financial discount and relevant joint-law assumptions are those declared in the formal model.
--
--   Mathematical relation:
--
--   $$
--   V=a_G+\rho a_R+V_{\text{death riders}}
--   $$
-- source:
--   Originally derived two-life finite-grid definition or theorem, motivated by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapter 10, Section 10.6, p. 150. The published reference supplies actuarial context, while the formal statement and joint-law conventions are new. https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_d_advancedValue
import Definitions.Def_actuarial_d_deferGuaranteed
import Definitions.Def_actuarial_d_deferBlockedRev
import Definitions.Def_actuarial_d_assureFirst
import Definitions.Def_actuarial_d_assureSecond
import Definitions.Def_actuarial_d_assureXFirst
import Definitions.Def_actuarial_d_assureYFirst
import Definitions.Def_actuarial_d_assureTie

open ActuarialJointD

theorem actuarial_d_advanced_occupation_reconciliation (h a n g : ℕ) (p : ℕ → ℕ → ℝ) (d b : ℕ → ℝ) (rho f s fx fy ft : ℝ) : advancedValue h a n g p d b rho f s fx fy ft = deferGuaranteed h a n g p d b + rho * deferBlockedRev h a n g p d b + f * assureFirst h p d + s * assureSecond h p d + fx * assureXFirst h p d + fy * assureYFirst h p d + ft * assureTie h p d := by sorry
