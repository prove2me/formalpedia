-- Prove2me | Theorems.Thm_actuarial_f_post88_gmp_no_october_april_uplift
-- name    : actuarial_f_post88_gmp_no_october_april_uplift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:27:40.827963+00:00
-- url     : https://prove2.me/theorems/e5e85a03-bd43-4db5-8de7-8095869044e4
-- title:
--   No statutory uplift on 5 April before first due event
-- statement:
--   A payment effective on 5 April 2027 does not yet reflect the first 6 April 2027 post-88 GMP increase.
--
--   The asserted result is:
--
--   $$
--   u_{2027,5\mathrm{Apr}}=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF

theorem actuarial_f_post88_gmp_no_october_april_uplift :
    gmpPost88AprilIncrease 20261001 20270405
      (fun _ => (7 / 100 : ℝ)) 2027 = 0 := by
  sorry
