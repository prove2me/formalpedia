-- Prove2me | Theorems.Thm_actuarial_f_nonstatutory_spouse_surplus_displaceable
-- name    : actuarial_f_nonstatutory_spouse_surplus_displaceable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:32:10.126148+00:00
-- url     : https://prove2.me/theorems/1b26e8ef-b3ca-4c22-b709-2f333a639654
-- title:
--   Survivor overlap excludes protected statutory minimum
-- statement:
--   Survivor overlap excludes protected statutory minimum. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpProtectedSurvivorDisplaceable

open ActuarialUnderpinsF

theorem actuarial_f_nonstatutory_spouse_surplus_displaceable
    (scheme statutory : ℝ) :
    gmpProtectedSurvivorDisplaceable True scheme statutory =
      max 0 (scheme - statutory) := by
  sorry
