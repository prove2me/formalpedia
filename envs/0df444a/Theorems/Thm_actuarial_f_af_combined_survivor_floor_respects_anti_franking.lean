-- Prove2me | Theorems.Thm_actuarial_f_af_combined_survivor_floor_respects_anti_franking
-- name    : actuarial_f_af_combined_survivor_floor_respects_anti_franking
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:36:14.633555+00:00
-- url     : https://prove2.me/theorems/479dc7c6-4873-4a23-8829-9ebe6b8ab00a
-- title:
--   Combined survivor minimum honours statutory anti-franking
-- statement:
--   Prove the combined protected survivor floor is no less than the converted section 87(2) aggregate. This result is an open Lean proof obligation, not a member-specific legal certification.
-- source:
--   Original derived statutory UK DB benefit contracts based on Pension Schemes Act 1993 sections 87–92 (including statutory relevant sum, appropriate addition, later earnings addition and exclusions), https://www.legislation.gov.uk/ukpga/1993/48/part/IV/chapter/III; and Pensions Act 1995 section 53 (next-year above-statutory credit and full deemed increase), https://www.legislation.gov.uk/ukpga/1995/26/section/53. Historic cessation-date definitions and GMP age, s88 pension-at-cessation or short service benefits, s89 additional accrual and postponement enhancements, and the s90(3) assumed earnings/GMP inputs must be certified member-by-member. The ordinary member/survivor branches exclude complete substituted benefits requiring alternative s87(3)(a) treatment, and do not by themselves implement all of sections 87–92, section 91 special service rules or s92 commutation disregard. Monetary inputs are weekly unless explicitly converted, and section 53 credits are already certified amounts.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afStatutoryWeeklyToMonthly
import Definitions.Def_actuarial_f_afSurvivorCombinedMinimum

open ActuarialUnderpinsF

theorem actuarial_f_af_combined_survivor_floor_respects_anti_franking
    (gmpMonthly antiFrankingWeekly : ℝ) :
    afStatutoryWeeklyToMonthly antiFrankingWeekly ≤
      afSurvivorCombinedMinimum gmpMonthly antiFrankingWeekly := by
  sorry
