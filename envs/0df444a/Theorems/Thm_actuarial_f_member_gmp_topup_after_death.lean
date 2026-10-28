-- Prove2me | Theorems.Thm_actuarial_f_member_gmp_topup_after_death
-- name    : actuarial_f_member_gmp_topup_after_death
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:29:17.232058+00:00
-- url     : https://prove2.me/theorems/419b5046-fefd-4a2d-bd59-469ff0a91b69
-- title:
--   GMP member top-up ceases with member payments
-- statement:
--   A member GMP top-up cannot be payable after the final member due instalment.
--
--   The asserted result is:
--
--   $$
--   t>i\Rightarrow T_t=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpMemberProtectedTopUp

open ActuarialUnderpinsF

theorem actuarial_f_member_gmp_topup_after_death
    (r z i t gpd : ℕ) (dateOf : ℕ → ℕ)
    (pre88 post88 protectedExcess : ℕ → ℝ)
    (orderRate a b c ga gb gc : ℕ → ℝ)
    (h : i < t) :
    gmpMemberProtectedTopUp r z i t gpd dateOf
      pre88 post88 protectedExcess orderRate a b c ga gb gc = 0 := by
  sorry
