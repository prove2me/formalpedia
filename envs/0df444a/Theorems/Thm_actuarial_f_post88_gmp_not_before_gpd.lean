-- Prove2me | Theorems.Thm_actuarial_f_post88_gmp_not_before_gpd
-- name    : actuarial_f_post88_gmp_not_before_gpd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:26:44.23937+00:00
-- url     : https://prove2.me/theorems/73358c4a-93f1-4b81-b3ba-cb3af9ddc1b7
-- title:
--   No 6 April GMP increase before GMP becomes payable
-- statement:
--   An event on or before the start of GMP entitlement is excluded from the post-88 increase sequence.
--
--   The asserted result is:
--
--   $$
--   t\le GPD\Rightarrow u_{y,t}=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPost88AprilIncrease

open ActuarialUnderpinsF

theorem actuarial_f_post88_gmp_not_before_gpd
    (gpd date year : ℕ) (orderRate : ℕ → ℝ)
    (h : date ≤ gpd) :
    gmpPost88AprilIncrease gpd date orderRate year = 0 := by
  sorry
