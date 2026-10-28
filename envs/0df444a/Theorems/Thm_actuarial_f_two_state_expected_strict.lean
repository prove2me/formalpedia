-- Prove2me | Theorems.Thm_actuarial_f_two_state_expected_strict
-- name    : actuarial_f_two_state_expected_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:10:57.69948+00:00
-- url     : https://prove2.me/theorems/17fc2b96-2a9d-454e-91ab-80ab1bae7e1c
-- title:
--   Two state expected strict
-- statement:
--   Two equally likely, opposing one-hundred-unit awards have expected maximum one hundred, despite marginal expected awards of fifty.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathbb E[\max(X,Y)]=100>50=\max(\mathbb E X,\mathbb E Y)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_awardBase
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem actuarial_f_two_state_expected_strict :
    let p : ℕ → ℕ → ℕ → ℝ := fun z i j =>
      if i = 0 ∧ j = 0 ∧ z < 2 then (1/2 : ℝ) else 0
    let a : ℕ → ℝ := fun z => if z = 0 then 100 else 0
    let b : ℕ → ℝ := fun z => if z = 1 then 100 else 0
    expect 2 0 p (fun z i j => awardBase a b z) = 100 ∧
      max (expect 2 0 p (fun z i j => a z))
          (expect 2 0 p (fun z i j => b z)) = 50 := by sorry
