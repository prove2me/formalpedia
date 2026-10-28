-- Prove2me | Theorems.Thm_actuarial_f_six_month_first_increase
-- name    : actuarial_f_six_month_first_increase
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:21:52.38651+00:00
-- url     : https://prove2.me/theorems/d14c1e35-b89b-42ce-8a25-e49b4b2b87b6
-- title:
--   Six-month first increase of two per cent
-- statement:
--   A four-per-cent annual increase with six complete months in payment produces a two-per-cent first increase.
--
--   The asserted result is:
--
--   $$
--   u_1=0.04(6/12)=0.02
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledRate

open ActuarialUnderpinsF

theorem actuarial_f_six_month_first_increase :
    monthlyScheduledRate 0 6 0 (5 / 100)
      (fun _ => (4 / 100 : ℝ)) 6 = (2 / 100 : ℝ) := by
  sorry
