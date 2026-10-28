-- Prove2me | Theorems.Thm_actuarial_f_survivor_replacement_respects_floor
-- name    : actuarial_f_survivor_replacement_respects_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T20:31:39.211997+00:00
-- url     : https://prove2.me/theorems/0449947f-7d49-43cb-a493-54676022e9ce
-- title:
--   Replacement must preserve statutory survivor GMP
-- statement:
--   Replacement must preserve statutory survivor GMP. This is a proof obligation on the exact declared Lean benefit contract. It does not certify scheme-specific legal inputs.
-- source:
--   Original derived UK DB pension valuation. Statutory context: PSA 1993 sections 17, 87–92 and 109, https://www.legislation.gov.uk/ukpga/1993/48/section/109; Pensions Act 1995 section 53, https://www.legislation.gov.uk/ukpga/1995/26/section/53; HMRC Pensions Tax Manual PTM071500, https://www.gov.uk/hmrc-internal-manuals/pensions-tax-manual/ptm071500. Full statutory anti-franking, allowable offset credits, GMP revaluation modes and exact survivor eligibility remain externally certified inputs. The estate guarantee replacement is a conditional illustrative contract, not a legal assertion.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_gmpProtectedSurvivorReplacement

open ActuarialUnderpinsF

theorem actuarial_f_survivor_replacement_respects_floor
    (replace : Prop) (scheme statutory : ℝ) :
    statutory ≤ gmpProtectedSurvivorReplacement replace scheme statutory := by
  sorry
