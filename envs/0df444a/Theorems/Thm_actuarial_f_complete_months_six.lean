-- Prove2me | Theorems.Thm_actuarial_f_complete_months_six
-- name    : actuarial_f_complete_months_six
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:21:36.777394+00:00
-- url     : https://prove2.me/theorems/62967460-88e5-4f1b-a431-147ba24f11bf
-- title:
--   Six complete months
-- statement:
--   An October-to-April style six-complete-month interval contributes six twelfths.
--
--   The asserted result is:
--
--   $$
--   m(0,6)=6
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_completeMonths

open ActuarialUnderpinsF

theorem actuarial_f_complete_months_six :
    completeMonths 0 6 = 6 := by
  sorry
