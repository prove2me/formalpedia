-- Prove2me | Theorems.Thm_actuarial_f_member_gmp_pre88_part_unchanged
-- name    : actuarial_f_member_gmp_pre88_part_unchanged
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:28:21.26543+00:00
-- url     : https://prove2.me/theorems/b06589ff-eeab-46b2-86b3-38b4e1e0bc63
-- title:
--   Statutory member floor retains unchanged pre-88 part
-- statement:
--   Only the post-88 component is increased under the section 109 rate in this split member GMP floor.
--
--   The asserted result is:
--
--   $$
--   G_t=G_-+G_+I_t
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88StatutoryGrowth
import Definitions.Def_actuarial_f_gmpMemberMinimumAtPayment

open ActuarialUnderpinsF

theorem actuarial_f_member_gmp_pre88_part_unchanged
    (pre88 post88 : ℝ) (gpd date : ℕ)
    (orderRate : ℕ → ℝ) :
    gmpMemberMinimumAtPayment pre88 post88 gpd date orderRate =
      pre88 + post88 * gmpPost88StatutoryGrowth gpd date orderRate := by
  sorry
