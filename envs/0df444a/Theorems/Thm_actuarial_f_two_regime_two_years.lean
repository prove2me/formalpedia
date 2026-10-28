-- Prove2me | Theorems.Thm_actuarial_f_two_regime_two_years
-- name    : actuarial_f_two_regime_two_years
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:08:52.601229+00:00
-- url     : https://prove2.me/theorems/6250ae92-9683-4413-b52f-42a7257a1fce
-- title:
--   Two regime two years
-- statement:
--   A two per cent deferred revaluation factor followed by a three per cent in-payment increase compounds multiplicatively, with the rates applied in different periods.
--
--   The defining or asserted relationship is:
--
--   $$
--   P_2=P_0(1.02)(1.03)
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_phasedPension

open ActuarialUnderpinsF

theorem actuarial_f_two_regime_two_years (base : ℝ) :
    phasedPension base 1 2 (fun _ => (2/100 : ℝ))
      (fun _ => (3/100 : ℝ)) = base * (102/100 : ℝ) * (103/100 : ℝ) := by sorry
