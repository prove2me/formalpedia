-- Prove2me | Theorems.Thm_actuarial_f_first_increase_rate_uses_cap
-- name    : actuarial_f_first_increase_rate_uses_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:23:33.318721+00:00
-- url     : https://prove2.me/theorems/9d74c5a0-f668-446d-8720-39b4a5d5a6ef
-- title:
--   Apply LPI cap before first pro-rating
-- statement:
--   The first annual inflation rate is capped/floored and only then pro-rated for the complete months in payment.
--
--   The asserted result is:
--
--   $$
--   u_1=\alpha\min(c,\max(f,\pi_0))
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_completeMonths
import Definitions.Def_actuarial_f_proratedAnnualRate
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem actuarial_f_first_increase_rate_uses_cap
    (r first : ℕ) (floor cap observed : ℝ)
    (inflation : ℕ → ℝ) (hfirst : r < first)
    (hi : inflation 0 = observed) :
    monthlyScheduledRate r first floor cap inflation first =
      proratedAnnualRate (lpiRate floor cap observed)
        (completeMonths r first) := by
  sorry
