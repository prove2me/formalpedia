-- Prove2me | Theorems.Thm_actuarial_f_post2005_illustrative_two_half_cap
-- name    : actuarial_f_post2005_illustrative_two_half_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:24:22.350015+00:00
-- url     : https://prove2.me/theorems/71e2e539-ddab-4133-9eb9-bab8e6c003e7
-- title:
--   Illustrative post-2005 two-and-half-per-cent cap
-- statement:
--   An illustrative eight-per-cent observation produces a capped rate of two-and-a-half per cent.
--
--   The asserted result is:
--
--   $$
--   u_{2.5}(0.08)=0.025
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_post05IllustrativeRate

open ActuarialUnderpinsF

theorem actuarial_f_post2005_illustrative_two_half_cap :
    post05IllustrativeRate (8 / 100) = (25 / 1000 : ℝ) := by
  sorry
