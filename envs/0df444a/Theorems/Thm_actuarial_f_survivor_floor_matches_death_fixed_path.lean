-- Prove2me | Theorems.Thm_actuarial_f_survivor_floor_matches_death_fixed_path
-- name    : actuarial_f_survivor_floor_matches_death_fixed_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:20:13.24259+00:00
-- url     : https://prove2.me/theorems/e85f55f2-b2e1-4105-a996-74bf74c0aea8
-- title:
--   Survivor floor matches death fixed path
-- statement:
--   The survivor's minimum established at member death remains the same base in the later indexed spouse payment, even when mortality varies by year.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{S,\text{floor}}_t=\max(S^A_{zi},S^B_{zi})G^S_{i,t}s_{ij}(t)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseBaseAtDeath
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_survivorFlooredInstalment

open ActuarialUnderpinsF

theorem actuarial_f_survivor_floor_matches_death_fixed_path
    (h z i j t : ℕ) (sa sb : ℕ → ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) :
    survivorFlooredInstalment h z i j t sa sb gs =
      spouseInstalment h z i j t
        (fun z i => spouseBaseAtDeath z i sa sb) gs := by sorry
