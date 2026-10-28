-- Prove2me | Theorems.Thm_actuarial_f_post88_gmp_full_three_percent_example
-- name    : actuarial_f_post88_gmp_full_three_percent_example
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:27:31.902823+00:00
-- url     : https://prove2.me/theorems/95d59d5b-22bb-4ae0-9f38-ebe318ec4cc4
-- title:
--   October GPD to 6 April earns full three per cent
-- statement:
--   A GMP payable from 1 October 2026 receives the full capped statutory 3% on 6 April 2027 if that year's order is 7% before the 3% cap.
--
--   The asserted result is:
--
--   $$
--   u_{2027}=0.03
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF

theorem actuarial_f_post88_gmp_full_three_percent_example :
    gmpPost88AprilIncrease 20261001 20270406
      (fun _ => (7 / 100 : ℝ)) 2027 = (3 / 100 : ℝ) := by
  sorry
