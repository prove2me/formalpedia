-- Prove2me | Theorems.Thm_actuarial_f_root_two_tranche_underpin_reconciliation
-- name    : actuarial_f_root_two_tranche_underpin_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:18:56.044897+00:00
-- url     : https://prove2.me/theorems/529540e3-e0f0-454b-944d-a18821fa14b8
-- title:
--   Root two tranche underpin reconciliation
-- statement:
--   A joint-life, two-tranche pension with an award-date maximum and separate growth paths has identical cashflow-first and benefit-state-first values; the first-tranche award maximum also dominates each fixed alternative under the stated positivity assumptions.
--
--   The defining or asserted relationship is:
--
--   $$
--   V^{\text{direct}}=V^{\text{state}},\qquad V_U\ge\max(V_A,V_B)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_directEPV
import Definitions.Def_actuarial_f_firstAwardPV
import Definitions.Def_actuarial_f_firstOptionPV
import Definitions.Def_actuarial_f_stateEPV

open ActuarialUnderpinsF

theorem actuarial_f_root_two_tranche_underpin_reconciliation
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (hv : 0 < n ∧
      (∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h + 1),
        ∀ j ∈ Finset.range (h + 1), 0 ≤ p z i j) ∧
      (∑ z ∈ Finset.range n, ∑ i ∈ Finset.range (h + 1),
        ∑ j ∈ Finset.range (h + 1), p z i j) = 1)
    (hd : ∀ t ∈ Finset.range (h + 1), 0 ≤ disc t)
    (hg : ∀ t ∈ Finset.range (h + 1), 0 ≤ g0 t) :
    directEPV n h r g p disc a b c s estate g0 g1 gs ge =
        stateEPV n h r g p disc a b c s estate g0 g1 gs ge ∧
      max (firstOptionPV n h r p disc a g0)
          (firstOptionPV n h r p disc b g0) ≤
        firstAwardPV n h r p disc a b g0 := by sorry
