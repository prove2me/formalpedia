-- Prove2me | Theorems.Thm_actuarial_f_day_prorating_full_period
-- name    : actuarial_f_day_prorating_full_period
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:23:47.28897+00:00
-- url     : https://prove2.me/theorems/750023d9-13c6-41ee-9ae3-6e1a9e37af32
-- title:
--   Full reference period earns full daily rate
-- statement:
--   Under the explicitly defined daily-fraction method, one entire reference period produces the whole annual rate.
--
--   The asserted result is:
--
--   $$
--   d=D>0\Longrightarrow u_{\mathrm{day}}=u
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_proratedDayRate

open ActuarialUnderpinsF

theorem actuarial_f_day_prorating_full_period
    (rate : ℝ) (yearDays : ℕ) (hpos : 0 < yearDays) :
    proratedDayRate rate yearDays yearDays = rate := by
  sorry
