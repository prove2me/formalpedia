-- Prove2me | Theorems.Thm_actuarial_f_member_gmp_topup_before_gpd
-- name    : actuarial_f_member_gmp_topup_before_gpd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:29:06.330758+00:00
-- url     : https://prove2.me/theorems/522ee078-93d1-455a-bbf5-ecb4bcb13fde
-- title:
--   No GMP top-up before the member GMP payable date
-- statement:
--   Where a dated instalment precedes GMP becoming payable, the supplemental protected-GMP layer contributes zero.
--
--   The asserted result is:
--
--   $$
--   t<GPD\Rightarrow T_t=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpMemberProtectedTopUp

open ActuarialUnderpinsF

theorem actuarial_f_member_gmp_topup_before_gpd
    (r z i t gpd : ℕ) (dateOf : ℕ → ℕ)
    (pre88 post88 protectedExcess : ℕ → ℝ)
    (orderRate a b c ga gb gc : ℕ → ℝ)
    (h : dateOf t < gpd) :
    gmpMemberProtectedTopUp r z i t gpd dateOf
      pre88 post88 protectedExcess orderRate a b c ga gb gc = 0 := by
  sorry
