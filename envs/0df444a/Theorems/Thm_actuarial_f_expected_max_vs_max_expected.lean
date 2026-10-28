-- Prove2me | Theorems.Thm_actuarial_f_expected_max_vs_max_expected
-- name    : actuarial_f_expected_max_vs_max_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:10:48.343396+00:00
-- url     : https://prove2.me/theorems/dc75f5c3-6625-44d7-a54d-ac5f46630740
-- title:
--   Expected max vs max expected
-- statement:
--   Expected award-date maximum dominates the greater of the two marginal expected alternative awards; no independence is imposed.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathbb E_p[\max(A_z,B_z)]\ge\max(\mathbb E_p[A_z],\mathbb E_p[B_z])
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem actuarial_f_expected_max_vs_max_expected (n h : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (a b : ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j) :
    max (expect n h p (fun z i j => a z))
        (expect n h p (fun z i j => b z)) ≤
      expect n h p (fun z i j => awardBase a b z) := by sorry
