-- Prove2me | Theorems.Thm_actuarial_f_monthly_growth_first_increase
-- name    : actuarial_f_monthly_growth_first_increase
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:23:15.092005+00:00
-- url     : https://prove2.me/theorems/4c1e4c6f-d0ce-4cd7-b773-fc2c99014184
-- title:
--   First increase applies exactly once
-- statement:
--   At the first increase month the multiplier equals one plus the pro-rated first-event rate.
--
--   The asserted result is:
--
--   $$
--   G_{D_1}=1+\alpha u_0
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_completeMonths
import Definitions.Def_actuarial_f_proratedAnnualRate
import Definitions.Def_actuarial_f_monthlyScheduledGrowth

open ActuarialUnderpinsF

theorem actuarial_f_monthly_growth_first_increase
    (r first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hr : r < first) :
    monthlyScheduledGrowth r first floor cap inflation first =
      1 + proratedAnnualRate (lpiRate floor cap (inflation 0))
            (completeMonths r first) := by
  sorry
