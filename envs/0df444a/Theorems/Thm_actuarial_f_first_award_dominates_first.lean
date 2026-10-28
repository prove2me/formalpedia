-- Prove2me | Theorems.Thm_actuarial_f_first_award_dominates_first
-- name    : actuarial_f_first_award_dominates_first
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:11:23.895838+00:00
-- url     : https://prove2.me/theorems/65fc8ddc-64ba-42ad-bf72-e830416fddab
-- title:
--   First award dominates first
-- statement:
--   Under nonnegative discount, growth and state masses, the first-tranche liability with an award underpin dominates the liability with first award base only.
--
--   The defining or asserted relationship is:
--
--   $$
--   V_U\ge V_A
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), Chapter 20 (financial options), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_firstAwardPV
import Definitions.Def_actuarial_f_firstOptionPV

open ActuarialUnderpinsF

theorem actuarial_f_first_award_dominates_first (n h r : ℕ)
    (p : ℕ → ℕ → ℕ → ℝ) (disc a b growth : ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j)
    (hd : ∀ t ∈ Finset.range (h+1), 0 ≤ disc t)
    (hg : ∀ t ∈ Finset.range (h+1), 0 ≤ growth t) :
    firstOptionPV n h r p disc a growth ≤
      firstAwardPV n h r p disc a b growth := by sorry
