-- Prove2me | Theorems.Thm_actuarial_f_expect_scale
-- name    : actuarial_f_expect_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:03:27.165922+00:00
-- url     : https://prove2.me/theorems/0c481f93-c98a-4aeb-92cc-59a7ece59e1b
-- title:
--   Expect scale
-- statement:
--   Scaling every scenario's cash benefit by a fixed real amount scales the expected benefit by the same amount.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathbb E_p[cX]=c\mathbb E_p[X]
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem actuarial_f_expect_scale (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (f : ℕ → ℕ → ℕ → ℝ) (c : ℝ) :
    expect n h p (fun z i j => c * f z i j) = c * expect n h p f := by sorry
