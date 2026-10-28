-- Prove2me | Theorems.Thm_actuarial_f_overlap_difference
-- name    : actuarial_f_overlap_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:14:32.6808+00:00
-- url     : https://prove2.me/theorems/ebd031d0-709b-4482-8348-fd0d85767e9d
-- title:
--   Overlap difference
-- statement:
--   The parallel-minus-replacement difference is precisely the spouse payment on the dates when estate guarantee instalments would otherwise replace it.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^{\text{par}}_t-C^{\text{rep}}_t=C^S_t\mathbf1_{\{e_i(t)=1\}}
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_estateDue
import Definitions.Def_actuarial_f_parallelPayment
import Definitions.Def_actuarial_f_replacementPayment
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem actuarial_f_overlap_difference (h r g z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ) :
    parallelPayment h r g z i j t s gs estateBase ge -
      replacementPayment h r g z i j t s gs estateBase ge =
        if estateDue h r g i t = 1 then
          spouseInstalment h z i j t s gs else 0 := by sorry
