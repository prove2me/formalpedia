-- Prove2me | Theorems.Thm_actuarial_f_no_retirement_increase
-- name    : actuarial_f_no_retirement_increase
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:22:55.121363+00:00
-- url     : https://prove2.me/theorems/b9640a1a-ddf0-4361-ac9c-8e53bd753d9e
-- title:
--   Pension has no pre-award in-payment uplift
-- statement:
--   At retirement the growth multiplier is one when the first scheduled increase occurs later.
--
--   The asserted result is:
--
--   $$
--   G_R=1
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledGrowth

open ActuarialUnderpinsF

theorem actuarial_f_no_retirement_increase
    (r first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hr : r < first) :
    monthlyScheduledGrowth r first floor cap inflation r = 1 := by
  sorry
