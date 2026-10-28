-- Prove2me | Theorems.Thm_actuarial_f_anti_franking_illustrative_floor_above_current
-- name    : actuarial_f_anti_franking_illustrative_floor_above_current
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:28:34.41802+00:00
-- url     : https://prove2.me/theorems/8f210627-a856-4a50-9a61-10ea6956aadd
-- title:
--   Illustrative anti-franking floor does not reduce pension
-- statement:
--   The externally certified minimum preserves at least the contractual pension already due.
--
--   The asserted result is:
--
--   $$
--   P_{\min}\ge P_t
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpIllustrativeProtectedFloor

open ActuarialUnderpinsF

theorem actuarial_f_anti_franking_illustrative_floor_above_current
    (gmpMinimum protectedExcess current : ℝ) :
    current ≤ gmpIllustrativeProtectedFloor
      gmpMinimum protectedExcess current := by
  sorry
