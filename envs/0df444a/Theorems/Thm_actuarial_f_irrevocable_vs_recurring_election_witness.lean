-- Prove2me | Theorems.Thm_actuarial_f_irrevocable_vs_recurring_election_witness
-- name    : actuarial_f_irrevocable_vs_recurring_election_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:20:01.483985+00:00
-- url     : https://prove2.me/theorems/82acb5e8-96b7-49c2-8b9b-73db882eb2cc
-- title:
--   Irrevocable vs recurring election witness
-- statement:
--   A genuine two-payment contract distinguishes an award-date irrevocable winner, an ex-ante stream choice and repeated annual switching, each with a distinct total.
--
--   The three values in this exact finite-state example are:
--
--   $$
--   \begin{aligned}
--   V_{\text{award}} &=240\\
--   V_{\text{fixed stream}} &=400\\
--   V_{\text{recurring}} &=420
--   \end{aligned}
--   $$
--
--   These are different exercise arrangements, so the figures are not interchangeable.
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_annualFloorPayment
import Definitions.Def_actuarial_f_fixedChoicePayment

open ActuarialUnderpinsF

theorem actuarial_f_irrevocable_vs_recurring_election_witness :
    let a : ℕ → ℝ := fun _ => 120
    let b : ℕ → ℝ := fun _ => 100
    let ga : ℕ → ℝ := fun _ => 1
    let gb : ℕ → ℝ := fun t => if t = 0 then 1 else 3
    fixedChoicePayment a b ga gb 0 0 +
        fixedChoicePayment a b ga gb 0 1 = 240 ∧
      max (a 0 * ga 0 + a 0 * ga 1)
          (b 0 * gb 0 + b 0 * gb 1) = 400 ∧
      annualFloorPayment a b ga gb 0 0 +
        annualFloorPayment a b ga gb 0 1 = 420 := by sorry
