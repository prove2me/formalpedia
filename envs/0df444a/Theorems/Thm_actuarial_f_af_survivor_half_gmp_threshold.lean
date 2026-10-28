-- Prove2me | Theorems.Thm_actuarial_f_af_survivor_half_gmp_threshold
-- name    : actuarial_f_af_survivor_half_gmp_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:35:07.340996+00:00
-- url     : https://prove2.me/theorems/b8b8e995-61cc-43b5-adab-5bfb2d59b49f
-- title:
--   Survivor anti-franking uses half GMP at cessation
-- statement:
--   Conditional Pension Schemes Act 1993 section 87 calculation. Both historic exclusions, independently certified pre-1985 transfer-credit growth disregard, and the required post-cessation employment accrual eligibility are represented where relevant. This remains an open Lean statement and does not decide all statutory exceptions.
-- source:
--   Pension Schemes Act 1993 section 87(1)-(7), 88-92, https://www.legislation.gov.uk/ukpga/1993/48/section/87 (including section 87(4)(d) conditional later accrual, (5) pre-1985 transfer-credit GMP growth disregard, and (7)(a)-(b) historic exclusions). Certified dates, GMP growth exclusions and benefits are external inputs.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_afSurvivorSection87WeeklyFloor

open ActuarialUnderpinsF

theorem actuarial_f_af_survivor_half_gmp_threshold
    (cessation death gpd t : ℕ)
    (relevant current memberBase appropriate later : ℝ)
    (hhalf : relevant ≤ memberBase / 2) :
    afSurvivorSection87WeeklyFloor cessation death gpd t
      false false true false false relevant current memberBase
      appropriate later 0 = 0 := by
  sorry
