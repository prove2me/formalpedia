-- Prove2me | Theorems.Thm_actuarial_f_pre88_gmp_growth_one
-- name    : actuarial_f_pre88_gmp_growth_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:26:35.863386+00:00
-- url     : https://prove2.me/theorems/415d7dea-a5f8-44bf-802b-624d1f603629
-- title:
--   Pre-88 GMP section 109 growth is one
-- statement:
--   No section 109 statutory GMP inflation uplift is compounded on the pre-88 GMP component.
--
--   The asserted result is:
--
--   $$
--   G^{\mathrm{pre88}}_t=1
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpPre88StatutoryGrowth

open ActuarialUnderpinsF

theorem actuarial_f_pre88_gmp_growth_one
    (gpd date : ℕ) :
    gmpPre88StatutoryGrowth gpd date = 1 := by
  sorry
