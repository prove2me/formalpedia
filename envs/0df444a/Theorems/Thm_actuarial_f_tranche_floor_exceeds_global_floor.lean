-- Prove2me | Theorems.Thm_actuarial_f_tranche_floor_exceeds_global_floor
-- name    : actuarial_f_tranche_floor_exceeds_global_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:15:54.320281+00:00
-- url     : https://prove2.me/theorems/d3045c81-ebdc-4a49-baeb-ec3508d62913
-- title:
--   Tranche floor exceeds global floor
-- statement:
--   Per-tranche minima provide at least the pension obtained by taking a maximum only after adding each whole set of alternatives.
--
--   The defining or asserted relationship is:
--
--   $$
--   \sum_{k}\max(A_k,B_k)\ge\max\left(\sum_kA_k,\sum_kB_k\right)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapter 17 (embedded option valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow Chapter 20, financial option contracts begins at p. 337; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal
import Definitions.Def_actuarial_f_wholeFloorTotal

open ActuarialUnderpinsF

theorem actuarial_f_tranche_floor_exceeds_global_floor (a b : ℕ → ℝ) (k : ℕ) :
    wholeFloorTotal a b k ≤ trancheFloorTotal a b k := by sorry
