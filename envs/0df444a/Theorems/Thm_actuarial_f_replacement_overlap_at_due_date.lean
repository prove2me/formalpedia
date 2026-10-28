-- Prove2me | Theorems.Thm_actuarial_f_replacement_overlap_at_due_date
-- name    : actuarial_f_replacement_overlap_at_due_date
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:20:28.925456+00:00
-- url     : https://prove2.me/theorems/791e59bd-ef15-4921-9703-45db8dfaf26d
-- title:
--   Replacement overlap at due date
-- statement:
--   At each instalment date the parallel contract equals the guarantee-replacement payment plus the spouse amount restricted to the genuine overlap.
--
--   The defining or asserted relationship is:
--
--   $$
--   C_t=C^{\text{rep}}_t+C^S_t\mathbf1_{\{e_i(t)=1\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_replacementTotalInstalment
import Definitions.Def_actuarial_f_spouseInstalment
import Definitions.Def_actuarial_f_totalInstalment

open ActuarialUnderpinsF

theorem actuarial_f_replacement_overlap_at_due_date
    (h r g z i j t : ℕ) (a b c : ℕ → ℝ)
    (s : ℕ → ℕ → ℝ) (estate : ℕ → ℝ)
    (g0 g1 : ℕ → ℝ) (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    totalInstalment h r g z i j t a b c s estate g0 g1 gs ge =
      replacementTotalInstalment h r g z i j t a b c s estate g0 g1 gs ge +
        (if estateDue h r g i t = 1 then
           spouseInstalment h z i j t s gs else 0) := by sorry
