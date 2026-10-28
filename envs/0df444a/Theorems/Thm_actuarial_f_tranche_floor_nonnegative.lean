-- Prove2me | Theorems.Thm_actuarial_f_tranche_floor_nonnegative
-- name    : actuarial_f_tranche_floor_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:16:06.830877+00:00
-- url     : https://prove2.me/theorems/393870cb-9bff-4ab8-b42f-d162de1d9efe
-- title:
--   Tranche floor nonnegative
-- statement:
--   If all first-alternative tranche amounts are nonnegative, their corresponding per-tranche maximum amounts aggregate to a nonnegative pension.
--
--   The defining or asserted relationship is:
--
--   $$
--   A_k\ge0\Longrightarrow\sum_k\max(A_k,B_k)\ge0
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal

open ActuarialUnderpinsF

theorem actuarial_f_tranche_floor_nonnegative (a b : ℕ → ℝ) (k : ℕ)
    (ha : ∀ i ∈ Finset.range k, 0 ≤ a i) :
    0 ≤ trancheFloorTotal a b k := by sorry
