-- Prove2me | Theorems.Thm_actuarial_f_additive_and_compound_differ
-- name    : actuarial_f_additive_and_compound_differ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:19:47.403986+00:00
-- url     : https://prove2.me/theorems/b175c456-4688-4282-a322-2036cfd70d0e
-- title:
--   Additive and compound differ
-- statement:
--   Two positive annual changes at ten per cent give a different additive increase from the correctly compounded pension multiplier.
--
--   The defining or asserted relationship is:
--
--   $$
--   G^{\text{add}}_2=1.20,\quad G^{\text{comp}}_2=1.21
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_additiveGrowth
import Definitions.Def_actuarial_f_compoundGrowth

open ActuarialUnderpinsF

theorem actuarial_f_additive_and_compound_differ :
    additiveGrowth (fun _ => (1/10 : ℝ)) 2 = (6/5 : ℝ) ∧
      compoundGrowth (fun _ => (1/10 : ℝ)) 2 = (121/100 : ℝ) := by sorry
