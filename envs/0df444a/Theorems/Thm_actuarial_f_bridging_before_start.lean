-- Prove2me | Theorems.Thm_actuarial_f_bridging_before_start
-- name    : actuarial_f_bridging_before_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:16:44.439611+00:00
-- url     : https://prove2.me/theorems/06e6a322-06a8-462f-b2f1-01e9cb809fbc
-- title:
--   Bridging before start
-- statement:
--   A bridge pension is absent before its contractually specified commencement date.
--
--   The defining or asserted relationship is:
--
--   $$
--   t<t_{\text{start}}\Longrightarrow b(t)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_bridgeDue

open ActuarialUnderpinsF

theorem actuarial_f_bridging_before_start (start stop t : ℕ)
    (ht : t < start) : bridgeDue start stop t = 0 := by sorry
