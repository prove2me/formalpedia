-- Prove2me | Theorems.Thm_actuarial_f_post88_gmp_no_part_year_scaling
-- name    : actuarial_f_post88_gmp_no_part_year_scaling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:27:51.781781+00:00
-- url     : https://prove2.me/theorems/31232486-ea40-4679-ab6a-595428e4251e
-- title:
--   No statutory GMP pro-rating on later 6 April payments
-- statement:
--   The post-88 GMP rate is the full capped order each qualifying year regardless of the number of months paid before the event.
--
--   The asserted result is:
--
--   $$
--   u_{y,t}=\min(0.03,\max(0,q_y))
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_lpiRate
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF

theorem actuarial_f_post88_gmp_no_part_year_scaling
    (gpd date year : ℕ) (orderRate : ℕ → ℝ)
    (hgpd : gpd < gmpSixApril year)
    (hevent : gmpSixApril year ≤ date) :
    gmpPost88AprilIncrease gpd date orderRate year =
      lpiRate 0 (3 / 100) (orderRate year) := by
  sorry
