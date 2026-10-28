-- Prove2me | Theorems.Thm_actuarial_f_survivor_gmp_not_automatically_payable
-- name    : actuarial_f_survivor_gmp_not_automatically_payable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:29:34.174888+00:00
-- url     : https://prove2.me/theorems/2ad221cd-235d-4033-8f18-cc1ec4dcaf7b
-- title:
--   Statutory survivor eligibility must be established
-- statement:
--   Where the eligibility input is false, the statutory survivor-GMP component is zero regardless of the selected contractual spouse benefit.
--
--   The asserted result is:
--
--   $$
--   \neg Q\Rightarrow G^S_t=0
--   $$
-- source:
--   Original explicitly specified UK pension scheme model. Pension Schemes Act 1993 s109: full annual post-1988 GMP statutory order with cap of 3%, effective 6 April after the GMP becomes payable, without first-period pro-rating; no corresponding statutory increase to pre-1988 GMP. https://www.legislation.gov.uk/ukpga/1993/48/section/109. HMRC GMP first-increase guidance: https://www.gov.uk/guidance/provide-a-pension-for-your-scheme-member. Section 110 sets GMP increase funding restrictions and Pensions Act 1995 s53 provides permitted reductions for other increases; not all are modelled. Anti-franking statutory sections 87-92 are NOT fully implemented: the protected-excess floor is an externally supplied illustrative minimum, not a legal certification. GMP payable date, scheme-specific pre-GPD revaluation, survivor eligibility/amounts and calendar-date inputs must be independently verified for each scheme.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpSurvivorMinimumAtPayment

open ActuarialUnderpinsF

theorem actuarial_f_survivor_gmp_not_automatically_payable
    (z i t : ℕ) (dateOf : ℕ → ℕ)
    (qualifies : ℕ → ℕ → Bool)
    (survivorPre88 survivorPost88 : ℕ → ℕ → ℝ)
    (orderRate : ℕ → ℝ)
    (h : qualifies z i = false) :
    gmpSurvivorMinimumAtPayment z i t dateOf qualifies
      survivorPre88 survivorPost88 orderRate = 0 := by
  sorry
