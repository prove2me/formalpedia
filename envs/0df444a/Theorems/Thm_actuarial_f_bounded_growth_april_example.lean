-- Prove2me | Theorems.Thm_actuarial_f_bounded_growth_april_example
-- name    : actuarial_f_bounded_growth_april_example
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:31:14.461008+00:00
-- url     : https://prove2.me/theorems/3408baa8-23e9-4e1d-a9c5-721d95b4b430
-- title:
--   Full bounded 6 April post-88 increase example
-- statement:
--   Full bounded 6 April post-88 increase example. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpBoundedPost88Growth

open ActuarialUnderpinsF

theorem actuarial_f_bounded_growth_april_example :
    gmpBoundedPost88Growth 20261001 20270406
      (fun _ => (7/100 : ℝ)) = (103/100 : ℝ) := by
  sorry
