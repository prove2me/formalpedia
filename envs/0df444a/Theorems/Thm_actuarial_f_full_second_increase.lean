-- Prove2me | Theorems.Thm_actuarial_f_full_second_increase
-- name    : actuarial_f_full_second_increase
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:22:38.511573+00:00
-- url     : https://prove2.me/theorems/6984fab5-95f1-4584-bf5d-141e4f49e140
-- title:
--   Full annual rate at the second event
-- statement:
--   Exactly twelve calendar months after a valid first event, use the new capped annual rate without a second pro-rata adjustment.
--
--   The asserted result is:
--
--   $$
--   u_{D_1+12}=\operatorname{LPI}(\pi_1)
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem actuarial_f_full_second_increase
    (r first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hr : r < first) :
    monthlyScheduledRate r first floor cap inflation (first + 12) =
      lpiRate floor cap (inflation 1) := by
  sorry
