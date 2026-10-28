-- Prove2me | Theorems.Thm_actuarial_f_af_member_pre1985_not_automatically_covered
-- name    : actuarial_f_af_member_pre1985_not_automatically_covered
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:34:22.322988+00:00
-- url     : https://prove2.me/theorems/ad008dcc-dfc4-446f-ba58-703aaed4b0b7
-- title:
--   Pre-1985 contracted-out leavers are excluded
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afMemberSection87WeeklyFloor

open ActuarialUnderpinsF

theorem actuarial_f_af_member_pre1985_not_automatically_covered
    (cessation gpd t : ℕ)
    (entitled substitute : Bool)
    (relevant current base addition later : ℝ) :
    afMemberSection87WeeklyFloor cessation gpd t
      true false entitled substitute false relevant current base
      addition later 0 = 0 := by
  sorry
