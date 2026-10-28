-- Prove2me | Theorems.Thm_actuarial_f_post88_gmp_not_on_gpd_april
-- name    : actuarial_f_post88_gmp_not_on_gpd_april
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:26:56.396013+00:00
-- url     : https://prove2.me/theorems/536a42f1-52df-40b4-8e92-6f93ab5a8064
-- title:
--   GMP commencing on 6 April waits for later 6 April
-- statement:
--   The event on the actual commencement day is excluded because the statutory first increase follows commencement.
--
--   The asserted result is:
--
--   $$
--   GPD=D_y\Rightarrow u_{y,D_y}=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpSixApril
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF

theorem actuarial_f_post88_gmp_not_on_gpd_april
    (year : ℕ) (orderRate : ℕ → ℝ) :
    gmpPost88AprilIncrease (gmpSixApril year)
      (gmpSixApril year) orderRate year = 0 := by
  sorry
