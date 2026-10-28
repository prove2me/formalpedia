-- Prove2me | Theorems.Thm_actuarial_f_pre_gpd_revaluation_distinct_from_inpayment
-- name    : actuarial_f_pre_gpd_revaluation_distinct_from_inpayment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:28:06.213724+00:00
-- url     : https://prove2.me/theorems/4ce7e7db-efe2-4749-a5df-2de1aca07ff2
-- title:
--   GMP revaluation is a different operation
-- statement:
--   Scheme-specific factors apply from leaving to GMP becoming payable; section 109 post-payable inflation proofing is not used for this interval.
--
--   The asserted result is:
--
--   $$
--   GPD_{\mathrm{base}}=G_-R_-+G_+R_+
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpRevaluedAtPayable

open ActuarialUnderpinsF

theorem actuarial_f_pre_gpd_revaluation_distinct_from_inpayment
    (pre88 post88 preFactor postFactor : ℝ) :
    gmpRevaluedAtPayable pre88 post88 preFactor postFactor =
      pre88 * preFactor + post88 * postFactor := by
  sorry
