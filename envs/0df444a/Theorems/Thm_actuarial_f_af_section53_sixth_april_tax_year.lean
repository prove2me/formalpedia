-- Prove2me | Theorems.Thm_actuarial_f_af_section53_sixth_april_tax_year
-- name    : actuarial_f_af_section53_sixth_april_tax_year
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:36:39.537222+00:00
-- url     : https://prove2.me/theorems/ceae2b1e-4d56-4aa7-8e2c-93355206baa3
-- title:
--   Section 53 new tax year on 6 April
-- statement:
--   Verify 6 April 2027 belongs to the 2027 tax year. This result is an open Lean proof obligation, not a member-specific legal certification.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afTaxYearFromYYYYMMDD

open ActuarialUnderpinsF

theorem actuarial_f_af_section53_sixth_april_tax_year :
    afTaxYearFromYYYYMMDD 20270406 = 2027 := by
  sorry
