-- Prove2me | Theorems.Thm_actuarial_f_spouse_start_after_death
-- name    : actuarial_f_spouse_start_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:04:56.504686+00:00
-- url     : https://prove2.me/theorems/06641b11-2de9-41e9-9b67-03fae09beb7a
-- title:
--   Spouse start after death
-- statement:
--   The continuation pension is absent on the member's own terminal-year index.
--
--   The defining or asserted relationship is:
--
--   $$
--   s_{ij}(i)=0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem actuarial_f_spouse_start_after_death (h i j : ℕ) :
    spouseDue h i j i = 0 := by sorry
