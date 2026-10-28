-- Prove2me | Theorems.Thm_actuarial_f_spouse_floor_monotone
-- name    : actuarial_f_spouse_floor_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:13:05.768203+00:00
-- url     : https://prove2.me/theorems/1f8acce9-529e-4e56-94be-a3bf5c1e4dc4
-- title:
--   Spouse floor monotone
-- statement:
--   With nonnegative survivor increases, a death-fixed spouse underpin cannot reduce a valid survivor instalment.
--
--   When the survivor increase multiplier is nonnegative, the payment satisfies:
--
--   $$
--   C^{S,\text{floor}}_t \ge S^A_{zi} G^S_{i,t}s_{ij}(t)
--   $$
--
--   This inequality uses the original spouse amount at member death, not a subsequently recalculated entitlement.
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_spouseDue
import Definitions.Def_actuarial_f_survivorFlooredInstalment

open ActuarialUnderpinsF

theorem actuarial_f_spouse_floor_monotone (h z i j t : ℕ)
    (a b : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (hg : 0 ≤ gs i t) :
    a z i * gs i t * spouseDue h i j t ≤
      survivorFlooredInstalment h z i j t a b gs := by sorry
