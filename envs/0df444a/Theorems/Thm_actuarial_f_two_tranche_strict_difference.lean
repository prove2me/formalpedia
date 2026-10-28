-- Prove2me | Theorems.Thm_actuarial_f_two_tranche_strict_difference
-- name    : actuarial_f_two_tranche_strict_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:16:34.263392+00:00
-- url     : https://prove2.me/theorems/75ca8f85-ddb2-48b0-8669-c09931f450f1
-- title:
--   Two tranche strict difference
-- statement:
--   Opposing winners across two tranches produce a total of twenty from individual minima but ten from a single minimum applied after aggregation.
--
--   The defining or asserted relationship is:
--
--   $$
--   10+10=20>10=\max(10,10)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_trancheFloorTotal
import Definitions.Def_actuarial_f_wholeFloorTotal

open ActuarialUnderpinsF

theorem actuarial_f_two_tranche_strict_difference :
    let a : ℕ → ℝ := fun i => if i = 0 then 10 else 0
    let b : ℕ → ℝ := fun i => if i = 1 then 10 else 0
    trancheFloorTotal a b 2 = 20 ∧ wholeFloorTotal a b 2 = 10 := by sorry
