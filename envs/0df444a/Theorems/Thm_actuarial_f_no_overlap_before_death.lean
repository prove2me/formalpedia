-- Prove2me | Theorems.Thm_actuarial_f_no_overlap_before_death
-- name    : actuarial_f_no_overlap_before_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:14:54.986043+00:00
-- url     : https://prove2.me/theorems/19354964-1c71-4d07-8e11-4a5af6c07f00
-- title:
--   No overlap before death
-- statement:
--   Before member death the coordination policies produce the same payment because the post-death guarantee is inactive.
--
--   The defining or asserted relationship is:
--
--   $$
--   t\le i\Longrightarrow C^{\text{par}}_t=C^{\text{rep}}_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §4.4, guaranteed life annuity payments begins at p. 53; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_parallelPayment
import Definitions.Def_actuarial_f_replacementPayment

open ActuarialUnderpinsF

theorem actuarial_f_no_overlap_before_death (h r g z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ) (ht : t ≤ i) :
    parallelPayment h r g z i j t s gs estateBase ge =
      replacementPayment h r g z i j t s gs estateBase ge := by sorry
