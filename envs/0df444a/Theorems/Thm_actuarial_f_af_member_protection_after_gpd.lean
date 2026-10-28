-- Prove2me | Theorems.Thm_actuarial_f_af_member_protection_after_gpd
-- name    : actuarial_f_af_member_protection_after_gpd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:34:39.753567+00:00
-- url     : https://prove2.me/theorems/fcd9894d-66a8-4145-913f-66cfde97feea
-- title:
--   Protected member pension after cessation and GMP growth
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afLaterEarningsAddition
import Definitions.Def_actuarial_f_afRelevantAggregateWeekly
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor

open ActuarialUnderpinsF

theorem actuarial_f_af_member_protection_after_gpd
    (cessation gpd t : ℕ)
    (relevant current base appropriate assumedLater excludedTransferGrowth : ℝ)
    (hcess : cessation < gpd) (hpay : gpd ≤ t)
    (hbase : base < relevant) (hgmp : base + excludedTransferGrowth < current) :
    afMemberSection87WeeklyFloor cessation gpd t
      false false true false true relevant current base appropriate
      (afLaterEarningsAddition relevant base assumedLater) excludedTransferGrowth =
    afRelevantAggregateWeekly relevant (current - base - excludedTransferGrowth)
       appropriate (afLaterEarningsAddition relevant base assumedLater) := by
  sorry
