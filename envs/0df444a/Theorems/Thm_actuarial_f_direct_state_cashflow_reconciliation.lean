-- Prove2me | Theorems.Thm_actuarial_f_direct_state_cashflow_reconciliation
-- name    : actuarial_f_direct_state_cashflow_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:18:34.115286+00:00
-- url     : https://prove2.me/theorems/bbc54232-08ee-4f8e-8205-55ff068c8bb0
-- title:
--   Direct state cashflow reconciliation
-- statement:
--   Scenario-first valuation equals valuation using independently stated member, survivor and estate cashflow paths under an arbitrary finite joint law.
--
--   The defining or asserted relationship is:
--
--   $$
--   \sum_{z,i,j}p_{zij}\sum_tv_tC_t=\sum_tv_t\sum_{z,i,j}p_{zij}C_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_directEPV
import Definitions.Def_actuarial_f_stateEPV

open ActuarialUnderpinsF

theorem actuarial_f_direct_state_cashflow_reconciliation
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    directEPV n h r g p disc a b c s estate g0 g1 gs ge =
      stateEPV n h r g p disc a b c s estate g0 g1 gs ge := by sorry
