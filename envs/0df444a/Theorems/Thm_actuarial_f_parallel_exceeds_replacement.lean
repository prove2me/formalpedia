-- Prove2me | Theorems.Thm_actuarial_f_parallel_exceeds_replacement
-- name    : actuarial_f_parallel_exceeds_replacement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:14:22.082675+00:00
-- url     : https://prove2.me/theorems/766a8d37-62dc-4e70-ace4-4f30b498892d
-- title:
--   Parallel exceeds replacement
-- statement:
--   With a nonnegative spouse payment, allowing estate and survivor payments in parallel never costs less than the corresponding replacement rule.
--
--   The defining or asserted relationship is:
--
--   $$
--   C^S_t\ge0\Longrightarrow C^{\text{par}}_t\ge C^{\text{rep}}_t
--   $$
-- source:
--   Original derived finite-scenario pension contract mathematics. Independent context: Dickson, Hardy and Waters (2020), Chapters 10 and 11 (contingent pensions and valuation), https://doi.org/10.1017/9781108784184; Promislow (2015), §13.3.1 (DB pensions), §§4.4 and 15.3 (guaranteed and stochastic annuities), https://www.wiley.com/en-us/Fundamentals+of+Actuarial+Mathematics%2C+3rd+Edition-p-9781118782460. The benefit switches, thresholds, annual maxima and survivor endpoints are explicit illustrative contract terms, not claimed textbook quotations or universally prescribed UK rights. The cited Promislow §13.3.1, defined benefit pension plans begins at p. 204; this is contextual source attribution rather than a claim that the custom pension rule occurs verbatim on that page.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_parallelPayment
import Definitions.Def_actuarial_f_replacementPayment
import Definitions.Def_actuarial_f_spouseInstalment

open ActuarialUnderpinsF

theorem actuarial_f_parallel_exceeds_replacement (h r g z i j t : ℕ)
    (s : ℕ → ℕ → ℝ) (gs : ℕ → ℕ → ℝ)
    (estateBase ge : ℕ → ℝ)
    (hsp : 0 ≤ spouseInstalment h z i j t s gs) :
    replacementPayment h r g z i j t s gs estateBase ge ≤
      parallelPayment h r g z i j t s gs estateBase ge := by sorry
