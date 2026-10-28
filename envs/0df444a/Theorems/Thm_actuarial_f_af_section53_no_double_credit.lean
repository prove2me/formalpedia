-- Prove2me | Theorems.Thm_actuarial_f_af_section53_no_double_credit
-- name    : actuarial_f_af_section53_no_double_credit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:37:02.941254+00:00
-- url     : https://prove2.me/theorems/bae2281f-a71b-4cee-8b9e-9b44e2df55aa
-- title:
--   Section 109 and section 51 credits must share a budget
-- statement:
--   A certified above-minimum increase cannot be fully credited to both statutory obligations. This result is an open Lean proof obligation, not a member-specific legal certification.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afSection53AllocationValid

open ActuarialUnderpinsF

theorem actuarial_f_af_section53_no_double_credit
    (available c109 c51 : ℝ)
    (valid : afSection53AllocationValid available c109 c51) :
    c109 + c51 ≤ max 0 available := by
  sorry
