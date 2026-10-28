-- Prove2me | Theorems.Thm_actuarial_f_post1988_gmp_three_percent_cap
-- name    : actuarial_f_post1988_gmp_three_percent_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:24:10.577381+00:00
-- url     : https://prove2.me/theorems/b134b11d-eedf-4126-b4dc-385dcc0c454e
-- title:
--   Post-1988 GMP illustrative three-per-cent cap
-- statement:
--   An illustrative six-per-cent inflation observation produces a three-per-cent capped rate.
--
--   The asserted result is:
--
--   $$
--   u_{\mathrm{GMP}}(0.06)=0.03
--   $$
-- source:
--   Original derived UK DB pension contract mathematics. Legal context: Pensions Act 1995 section 54(1)-(2), https://www.legislation.gov.uk/ukpga/1995/26/section/54. The complete-month first increase is a statutory minimum condition where the relevant section applies, not a universal discretionary scheme rule. Component rates, payment frequencies, survivor option links and index reference dates are explicitly chosen contract inputs and must be checked against scheme rules. Mathematical context: Dickson, Hardy and Waters (2020), chapters 10–11, https://doi.org/10.1017/9781108784184.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_post88GmpIllustrativeRate

open ActuarialUnderpinsF

theorem actuarial_f_post1988_gmp_three_percent_cap :
    post88GmpIllustrativeRate (6 / 100) = (3 / 100 : ℝ) := by
  sorry
