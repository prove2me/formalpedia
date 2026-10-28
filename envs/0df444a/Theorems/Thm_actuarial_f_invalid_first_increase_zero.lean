-- Prove2me | Theorems.Thm_actuarial_f_invalid_first_increase_zero
-- name    : actuarial_f_invalid_first_increase_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:22:08.514001+00:00
-- url     : https://prove2.me/theorems/93950975-6b69-4024-b14f-df57a1f1d2fe
-- title:
--   Invalid first-increase chronology earns no event
-- statement:
--   If the stated first increase date is not later than retirement the schedule deliberately provides zero event-rate rather than silently applying full rates.
--
--   The asserted result is:
--
--   $$
--   D_1\le R\Longrightarrow u_t=0
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem actuarial_f_invalid_first_increase_zero
    (r first t : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hf : first ≤ r) :
    monthlyScheduledRate r first floor cap inflation t = 0 := by
  sorry
