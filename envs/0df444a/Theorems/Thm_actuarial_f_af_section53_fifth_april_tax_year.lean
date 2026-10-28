-- Prove2me | Theorems.Thm_actuarial_f_af_section53_fifth_april_tax_year
-- name    : actuarial_f_af_section53_fifth_april_tax_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:36:26.850011+00:00
-- url     : https://prove2.me/theorems/bd450db5-22cf-43cc-8116-370ab1cd5a75
-- title:
--   Section 53 tax year before 6 April
-- statement:
--   Verify 5 April 2027 belongs to the 2026 tax year. This result is an open Lean proof obligation, not a member-specific legal certification.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afTaxYearFromYYYYMMDD

open ActuarialUnderpinsF

theorem actuarial_f_af_section53_fifth_april_tax_year :
    afTaxYearFromYYYYMMDD 20270405 = 2026 := by
  sorry
