-- Prove2me | Theorems.Thm_actuarial_f_expect_add
-- name    : actuarial_f_expect_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:03:12.529991+00:00
-- url     : https://prove2.me/theorems/a7217c63-75ee-4414-81fd-3edc5ab8babb
-- title:
--   Expect add
-- statement:
--   Under a common joint law, the expected value of adding two scenario-dependent benefit amounts is the sum of their separate expectations.
--
--   The defining or asserted relationship is:
--
--   $$
--   \mathbb E_p[X+Y]=\mathbb E_p[X]+\mathbb E_p[Y]
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem actuarial_f_expect_add (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (f g : ℕ → ℕ → ℕ → ℝ) :
    expect n h p (fun z i j => f z i j + g z i j) =
      expect n h p f + expect n h p g := by sorry
