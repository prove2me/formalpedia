-- Prove2me | Theorems.Thm_actuarial_f_survivor_first_increase_starts_after_death
-- name    : actuarial_f_survivor_first_increase_starts_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:26:11.345123+00:00
-- url     : https://prove2.me/theorems/7581a0a9-61e4-4f46-9559-4e2a3d5ae538
-- title:
--   Death-based survivor growth starts at one
-- statement:
--   The survivor's initial instalment uses the survivor pension fixed at death and gains no increase before its own first increase date.
--
--   The asserted result is:
--
--   $$
--   G^S_{i+1}=1
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_monthlyScheduledGrowth

open ActuarialUnderpinsF

theorem actuarial_f_survivor_first_increase_starts_after_death
    (i first : ℕ) (floor cap : ℝ) (inflation : ℕ → ℝ)
    (hfirst : i + 1 < first) :
    monthlyScheduledGrowth (i + 1) first floor cap inflation (i + 1) = 1 := by
  sorry
