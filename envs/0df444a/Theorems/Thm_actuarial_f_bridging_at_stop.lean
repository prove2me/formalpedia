-- Prove2me | Theorems.Thm_actuarial_f_bridging_at_stop
-- name    : actuarial_f_bridging_at_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:16:54.661471+00:00
-- url     : https://prove2.me/theorems/6c0ddb10-2e82-4cb3-8a22-2dddc82ee948
-- title:
--   Bridging at stop
-- statement:
--   A bridge pension ceases at its stated exclusive stop date.
--
--   The defining or asserted relationship is:
--
--   $$
--   b(t_{\text{stop}})=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeDue

open ActuarialUnderpinsF

theorem actuarial_f_bridging_at_stop (start stop : ℕ) :
    bridgeDue start stop stop = 0 := by sorry
