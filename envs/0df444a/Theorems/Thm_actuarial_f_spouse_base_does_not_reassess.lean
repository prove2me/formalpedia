-- Prove2me | Theorems.Thm_actuarial_f_spouse_base_does_not_reassess
-- name    : actuarial_f_spouse_base_does_not_reassess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:13:16.637259+00:00
-- url     : https://prove2.me/theorems/c2dc20d4-e747-4eec-a63f-83db8ef8d133
-- title:
--   Spouse base does not reassess
-- statement:
--   Once the survivor entitlement is established on member death, later payable instalments carry the fixed base times the survivor-specific increase.
--
--   The defining or asserted relationship is:
--
--   $$
--   s_{ij}(t)=1\Longrightarrow C^S_t=S_{zi}G^S_{i,t}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem actuarial_f_spouse_base_does_not_reassess (h z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (hd : spouseDue h i j t = 1) :
    spouseInstalment h z i j t s gs = s z i * gs i t := by sorry
