-- Prove2me | Theorems.Thm_actuarial_f_compound_nonnegative
-- name    : actuarial_f_compound_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:07:40.578718+00:00
-- url     : https://prove2.me/theorems/7392196c-87a6-466c-a5d1-c3a3f2893f18
-- title:
--   Compound nonnegative
-- statement:
--   Each gross annual factor being nonnegative ensures the compound pension multiplier is nonnegative.
--
--   The defining or asserted relationship is:
--
--   $$
--   \left(\forall k<t:\ell_k\ge-1\right)\Longrightarrow G_t\ge0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_compoundGrowth

open ActuarialUnderpinsF

theorem actuarial_f_compound_nonnegative (r : ℕ → ℝ) (t : ℕ)
    (hr : ∀ k ∈ Finset.range t, -1 ≤ r k) :
    0 ≤ compoundGrowth r t := by sorry
