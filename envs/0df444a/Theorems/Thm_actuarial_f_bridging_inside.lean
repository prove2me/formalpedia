-- Prove2me | Theorems.Thm_actuarial_f_bridging_inside
-- name    : actuarial_f_bridging_inside
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:17:04.649842+00:00
-- url     : https://prove2.me/theorems/d712fd31-992c-4b2a-a3c7-397995d03a4c
-- title:
--   Bridging inside
-- statement:
--   The contractual bridging payment is active at every date in the inclusive-start, exclusive-stop window.
--
--   The defining or asserted relationship is:
--
--   $$
--   t_{\text{start}}\le t<t_{\text{stop}}\Longrightarrow b(t)=1
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeDue

open ActuarialUnderpinsF

theorem actuarial_f_bridging_inside (start stop t : ℕ)
    (hs : start ≤ t) (ht : t < stop) :
    bridgeDue start stop t = 1 := by sorry
