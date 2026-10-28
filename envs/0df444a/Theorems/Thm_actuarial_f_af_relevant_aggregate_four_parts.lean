-- Prove2me | Theorems.Thm_actuarial_f_af_relevant_aggregate_four_parts
-- name    : actuarial_f_af_relevant_aggregate_four_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:33:56.538992+00:00
-- url     : https://prove2.me/theorems/0e8d2ae1-75b1-41eb-951f-5bd0c7edb1e0
-- title:
--   Four-part statutory anti-franking aggregate
-- statement:
--   Reconcile the section 87 weekly relevant aggregate with its component amounts. This result is an open Lean proof obligation, not a member-specific legal certification.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly

open ActuarialUnderpinsF

theorem actuarial_f_af_relevant_aggregate_four_parts
    (sum delta appropriate later : ℝ) :
    afRelevantAggregateWeekly sum delta appropriate later =
      sum + delta + appropriate + later := by
  sorry
