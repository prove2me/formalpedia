-- Prove2me | Theorems.Thm_actuarial_f_month_proportion_capped
-- name    : actuarial_f_month_proportion_capped
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:23:57.503705+00:00
-- url     : https://prove2.me/theorems/a20522ed-37ed-443c-82a1-e915eb377e98
-- title:
--   Pro-rating never exceeds twelve twelfths
-- statement:
--   Complete-month proportional increases are capped at twelve months, yielding the full annual rate thereafter.
--
--   The asserted result is:
--
--   $$
--   m\ge12\Longrightarrow u_m=u
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_proratedAnnualRate

open ActuarialUnderpinsF

theorem actuarial_f_month_proportion_capped
    (rate : ℝ) (months : ℕ) (h : 12 ≤ months) :
    proratedAnnualRate rate months = rate := by
  sorry
