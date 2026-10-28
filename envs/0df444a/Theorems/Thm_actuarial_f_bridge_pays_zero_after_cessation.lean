-- Prove2me | Theorems.Thm_actuarial_f_bridge_pays_zero_after_cessation
-- name    : actuarial_f_bridge_pays_zero_after_cessation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:17:15.754986+00:00
-- url     : https://prove2.me/theorems/48470460-c063-480e-b95b-1952866db0d3
-- title:
--   Bridge pays zero after cessation
-- statement:
--   A temporary bridging pension pays zero at and beyond its cessation date.
--
--   The defining or asserted relationship is:
--
--   $$
--   t\ge t_{\text{stop}}\Longrightarrow C^B_t=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeInstalment

open ActuarialUnderpinsF

theorem actuarial_f_bridge_pays_zero_after_cessation (start stop t : ℕ)
    (amount : ℝ) (ht : stop ≤ t) :
    bridgeInstalment start stop t amount = 0 := by sorry
