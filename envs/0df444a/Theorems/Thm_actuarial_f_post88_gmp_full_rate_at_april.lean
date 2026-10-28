-- Prove2me | Theorems.Thm_actuarial_f_post88_gmp_full_rate_at_april
-- name    : actuarial_f_post88_gmp_full_rate_at_april
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:27:20.652675+00:00
-- url     : https://prove2.me/theorems/36d07a40-4b9d-4af3-9210-2eef71dd7b22
-- title:
--   Full post-88 GMP order on first eligible 6 April
-- statement:
--   On each qualifying 6 April, the full annual statutory order rate is due rather than a proportional initial increase.
--
--   The asserted result is:
--
--   $$
--   u_{y,D_y}=q_y
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpStatutoryPost88OrderRate
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF

theorem actuarial_f_post88_gmp_full_rate_at_april
    (gpd year : ℕ) (orderRate : ℕ → ℝ)
    (h : gpd < gmpSixApril year) :
    gmpPost88AprilIncrease gpd (gmpSixApril year) orderRate year =
      gmpStatutoryPost88OrderRate orderRate year := by
  sorry
