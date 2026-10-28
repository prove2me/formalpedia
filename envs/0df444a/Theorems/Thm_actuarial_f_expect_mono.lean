-- Prove2me | Theorems.Thm_actuarial_f_expect_mono
-- name    : actuarial_f_expect_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:03:38.40702+00:00
-- url     : https://prove2.me/theorems/27c1acef-c68f-4d71-b708-db9252df8baf
-- title:
--   Expect mono
-- statement:
--   Nonnegative joint state masses preserve a pointwise ordering of pension benefit amounts after expected-value aggregation.
--
--   The defining or asserted relationship is:
--
--   $$
--   X\le Y\Longrightarrow\mathbb E_p[X]\le\mathbb E_p[Y]
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §15.3, stochastic life annuity valuation begins at p. 229; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_expect

open ActuarialUnderpinsF

theorem actuarial_f_expect_mono (n h : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (f g : ℕ → ℕ → ℕ → ℝ)
    (hp : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), 0 ≤ p z i j)
    (hfg : ∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h+1),
      ∀ j ∈ Finset.range (h+1), f z i j ≤ g z i j) :
    expect n h p f ≤ expect n h p g := by sorry
