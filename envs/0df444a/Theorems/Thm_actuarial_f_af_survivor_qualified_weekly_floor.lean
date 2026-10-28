-- Prove2me | Theorems.Thm_actuarial_f_af_survivor_qualified_weekly_floor
-- name    : actuarial_f_af_survivor_qualified_weekly_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:35:23.058343+00:00
-- url     : https://prove2.me/theorems/164a83cf-05cc-4f8e-ab43-f23769864b65
-- title:
--   Qualifying survivor anti-franking aggregate
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly
import Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor

open ActuarialUnderpinsF

theorem actuarial_f_af_survivor_qualified_weekly_floor
    (cessation death gpd t : ℕ)
    (relevant current memberBase appropriate later excludedTransferGrowth : ℝ)
    (hcess : cessation < min death gpd) (hpay : death < t)
    (hrel : memberBase / 2 < relevant)
    (hgmp : memberBase / 2 + excludedTransferGrowth < current) :
    afSurvivorSection87WeeklyFloor cessation death gpd t
      false false true false true relevant current memberBase
      appropriate later excludedTransferGrowth =
    afRelevantAggregateWeekly relevant (current - memberBase / 2 - excludedTransferGrowth)
      appropriate later := by
  sorry
