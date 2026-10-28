-- Prove2me | Theorems.Thm_actuarial_f_spouse_only_after_death
-- name    : actuarial_f_spouse_only_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:12:08.008446+00:00
-- url     : https://prove2.me/theorems/9f943e91-bc09-4771-a961-167edc0a275b
-- title:
--   Spouse only after death
-- statement:
--   A payable continuation instalment necessarily occurs after member death while the survivor is still entitled.
--
--   The defining or asserted relationship is:
--
--   $$
--   s_{ij}(t)=1\Longrightarrow i<t\le j
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue

open ActuarialUnderpinsF

theorem actuarial_f_spouse_only_after_death (h i j t : ℕ)
    (hs : spouseDue h i j t = 1) : i < t ∧ t ≤ j := by sorry
